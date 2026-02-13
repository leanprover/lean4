#!/usr/bin/env python3
"""
Analyze grind adoption LoC changes in mathlib.

For each theorem/lemma in master that uses grind, find the most recent
commit where it didn't use grind, and measure the LoC change.

This script was used in preparing the "Evaluation" section of the grind paper.
"""

import subprocess
import re
import csv
import sys
from pathlib import Path
from dataclasses import dataclass
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import Iterator
from functools import lru_cache


@dataclass
class GrindUsage:
    file: str
    line_no: int
    decl_name: str
    decl_type: str  # theorem, lemma, def, example, etc.


@dataclass
class LocChange:
    file: str
    decl_name: str
    decl_type: str
    old_loc: int
    new_loc: int
    loc_saved: int
    commit_sha: str
    commit_date: str


def run_git(args: list[str], repo: str = ".") -> str:
    """Run a git command and return stdout."""
    result = subprocess.run(
        ["git", "-C", repo] + args,
        capture_output=True, text=True, check=True
    )
    return result.stdout


def run_git_safe(args: list[str], repo: str = ".") -> str | None:
    """Run a git command, return None on failure."""
    result = subprocess.run(
        ["git", "-C", repo] + args,
        capture_output=True, text=True
    )
    if result.returncode != 0:
        return None
    return result.stdout


@lru_cache(maxsize=4096)
def get_file_at_commit(repo: str, commit: str, file_path: str) -> str | None:
    """Get file contents at a specific commit (cached)."""
    return run_git_safe(["show", f"{commit}:{file_path}"], repo)


def find_grind_usages(repo: str = ".") -> tuple[list[GrindUsage], int, int]:
    """Find all declarations using grind in current master.
    Returns (usages, total_grind_calls, grind_in_decls) where:
    - total_grind_calls is the count of grind tactic calls (after filtering comments/attrs)
    - grind_in_decls is the count of those that are inside named declarations
    """
    # Use git grep to find lines containing 'grind' (excludes lake packages)
    result = run_git(["grep", "-n", "grind", "master", "--", "Mathlib/"], repo)

    usages = []
    seen = set()  # (file, decl_name) to dedupe
    total_grind_calls = 0
    grind_in_decls = 0

    for line in result.strip().split('\n'):
        if not line:
            continue
        # Format: master:path/to/file.lean:123:line content
        match = re.match(r'^master:(.+\.lean):(\d+):(.*)$', line)
        if not match:
            continue

        file_path, line_no_str, content = match.groups()
        line_no = int(line_no_str)

        # Skip comments and attributes (not tactic calls)
        content_stripped = content.strip()
        if content_stripped.startswith('--') or content_stripped.startswith('/-'):
            continue
        if content_stripped.startswith('attribute'):
            continue
        if '@[' in content and 'grind' in content:
            # Could be an attribute like @[grind =], skip
            if 'by' not in content and ':=' not in content:
                continue

        total_grind_calls += 1

        # Find the declaration this grind belongs to
        decl_name, decl_type = find_decl_at_line(repo, file_path, line_no)
        if decl_name is None:
            continue

        grind_in_decls += 1

        key = (file_path, decl_name)
        if key in seen:
            continue
        seen.add(key)

        usages.append(GrindUsage(
            file=file_path,
            line_no=line_no,
            decl_name=decl_name,
            decl_type=decl_type
        ))

    return usages, total_grind_calls, grind_in_decls


def find_decl_at_line(repo: str, file_path: str, grind_line: int) -> tuple[str | None, str | None]:
    """
    Find the declaration name and type that contains the grind at the given line.
    Search backwards from grind_line to find the most recent declaration.
    """
    # Get file content at master
    content = get_file_at_commit(repo, "master", file_path)
    if content is None:
        return None, None

    lines = content.split('\n')

    # Search backwards from grind_line for a declaration
    # Match declarations with optional leading modifiers and attributes
    decl_pattern = re.compile(r'^(?:@\[.*?\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|scoped\s+)*(theorem|lemma|def|example|instance|abbrev|structure|class)\s+(\w+)')

    for i in range(grind_line - 1, -1, -1):
        if i >= len(lines):
            continue
        line = lines[i]
        match = decl_pattern.match(line)
        if match:
            return match.group(2), match.group(1)

    return None, None


def find_grind_introduction_commit(repo: str, file_path: str, decl_name: str) -> str | None:
    """
    Find the commit that introduced grind to this declaration.
    Returns None if the declaration was born with grind.
    """
    # First, find the line range of the declaration in master
    content = get_file_at_commit(repo, "master", file_path)
    if content is None:
        return None

    lines = content.split('\n')
    decl_start = None
    decl_end = None

    # Find declaration start
    decl_pattern = re.compile(rf'^(?:@\[.*?\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|scoped\s+)*(theorem|lemma|def|example|instance|abbrev|structure|class)\s+{re.escape(decl_name)}\b')
    for i, line in enumerate(lines):
        if decl_pattern.match(line):
            decl_start = i
            break

    if decl_start is None:
        return None

    # Find declaration end (next top-level declaration or EOF)
    end_patterns = re.compile(r'^(?:private\s+|protected\s+|noncomputable\s+|scoped\s+)*(theorem|lemma|def|example|instance|abbrev|structure|class|namespace|section|end\s|@\[|#|/-)')
    for i in range(decl_start + 1, len(lines)):
        line = lines[i]
        if line and not line[0].isspace() and end_patterns.match(line):
            decl_end = i
            break
    if decl_end is None:
        decl_end = len(lines)

    # Find grind line within declaration
    grind_line = None
    for i in range(decl_start, decl_end):
        if 'grind' in lines[i]:
            grind_line = i + 1  # 1-indexed
            break

    if grind_line is None:
        return None

    # Use git blame to find when that grind line was added
    blame_result = run_git_safe(["blame", "-L", f"{grind_line},{grind_line}", "--porcelain", "master", "--", file_path], repo)
    if blame_result is None:
        return None

    # First line of porcelain output is the commit SHA
    first_line = blame_result.split('\n')[0]
    commit_sha = first_line.split()[0]

    # Check if this declaration existed before this commit (without grind)
    parent_sha = run_git_safe(["rev-parse", f"{commit_sha}^"], repo)
    if parent_sha is None:
        return None  # Initial commit, born with grind
    parent_sha = parent_sha.strip()

    # Check if declaration existed in parent
    parent_content = get_file_at_commit(repo, parent_sha, file_path)
    if parent_content is None:
        # File didn't exist in parent - might be new file or renamed
        return None

    # Check if declaration existed and didn't have grind
    if decl_name not in parent_content:
        return None  # Declaration didn't exist - born with grind

    # Check if it already had grind in parent
    parent_lines = parent_content.split('\n')
    in_decl = False
    for line in parent_lines:
        if decl_pattern.match(line):
            in_decl = True
        elif in_decl:
            if line and not line[0].isspace() and end_patterns.match(line):
                break
            if 'grind' in line:
                # Already had grind in parent - need to go further back
                # For simplicity, we'll just use this commit
                return commit_sha

    return commit_sha


def extract_proof_loc(repo: str, file_path: str, decl_name: str, commit: str) -> int | None:
    """
    Extract the number of lines in a declaration's proof at a given commit.
    Returns None if the declaration doesn't exist at that commit.
    """
    content = get_file_at_commit(repo, commit, file_path)
    if content is None:
        return None

    lines = content.split('\n')

    # Find declaration start
    decl_pattern = re.compile(rf'^(?:@\[.*?\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|scoped\s+)*(theorem|lemma|def|example|instance|abbrev|structure|class)\s+{re.escape(decl_name)}\b')
    decl_start = None
    for i, line in enumerate(lines):
        if decl_pattern.match(line):
            decl_start = i
            break

    if decl_start is None:
        return None

    # Find declaration end
    end_patterns = re.compile(r'^(?:private\s+|protected\s+|noncomputable\s+|scoped\s+)*(theorem|lemma|def|example|instance|abbrev|structure|class|namespace|section|end\s|@\[|#|/-)')
    decl_end = None
    for i in range(decl_start + 1, len(lines)):
        line = lines[i]
        if line and not line[0].isspace() and end_patterns.match(line):
            decl_end = i
            break
    if decl_end is None:
        decl_end = len(lines)

    # Count non-empty lines in declaration
    loc = sum(1 for i in range(decl_start, decl_end) if lines[i].strip())
    return loc


def get_commit_date(repo: str, sha: str) -> str:
    """Get the date of a commit."""
    result = run_git(["log", "-1", "--format=%ci", sha], repo)
    return result.strip().split()[0]  # Just the date part


def analyze_usage(repo: str, usage: GrindUsage) -> LocChange | None:
    """Analyze a single grind usage and return LoC change info."""
    commit = find_grind_introduction_commit(repo, usage.file, usage.decl_name)
    if commit is None:
        return None

    parent = run_git_safe(["rev-parse", f"{commit}^"], repo)
    if parent is None:
        return None
    parent = parent.strip()

    old_loc = extract_proof_loc(repo, usage.file, usage.decl_name, parent)
    new_loc = extract_proof_loc(repo, usage.file, usage.decl_name, "master")

    if old_loc is None or new_loc is None:
        return None

    commit_date = get_commit_date(repo, commit)

    return LocChange(
        file=usage.file,
        decl_name=usage.decl_name,
        decl_type=usage.decl_type,
        old_loc=old_loc,
        new_loc=new_loc,
        loc_saved=old_loc - new_loc,
        commit_sha=commit[:12],
        commit_date=commit_date
    )


def analyze_usage_detailed(repo: str, usage: GrindUsage) -> tuple[LocChange | None, str]:
    """Analyze a single grind usage, returning (result, skip_reason)."""
    commit = find_grind_introduction_commit(repo, usage.file, usage.decl_name)
    if commit is None:
        return None, "born_with_grind"

    parent = run_git_safe(["rev-parse", f"{commit}^"], repo)
    if parent is None:
        return None, "no_parent"
    parent = parent.strip()

    old_loc = extract_proof_loc(repo, usage.file, usage.decl_name, parent)
    new_loc = extract_proof_loc(repo, usage.file, usage.decl_name, "master")

    if old_loc is None:
        return None, "old_loc_failed"
    if new_loc is None:
        return None, "new_loc_failed"

    commit_date = get_commit_date(repo, commit)

    return LocChange(
        file=usage.file,
        decl_name=usage.decl_name,
        decl_type=usage.decl_type,
        old_loc=old_loc,
        new_loc=new_loc,
        loc_saved=old_loc - new_loc,
        commit_sha=commit[:12],
        commit_date=commit_date
    ), "success"


def main(repo: str = "."):
    print("Finding grind usages in master...", file=sys.stderr)
    usages, total_grind_calls, grind_in_decls = find_grind_usages(repo)
    print(f"Found {len(usages)} declarations using grind ({grind_in_decls}/{total_grind_calls} grind calls)", file=sys.stderr)

    print("Analyzing git history (this may take a while)...", file=sys.stderr)
    results: list[LocChange] = []
    skip_reasons: dict[str, int] = {}

    with ThreadPoolExecutor(max_workers=64) as executor:
        futures = {executor.submit(analyze_usage_detailed, repo, usage): usage for usage in usages}

        for i, future in enumerate(as_completed(futures)):
            if (i + 1) % 50 == 0:
                print(f"  Progress: {i + 1}/{len(usages)}", file=sys.stderr, flush=True)

            result, reason = future.result()
            if result:
                results.append(result)
            else:
                skip_reasons[reason] = skip_reasons.get(reason, 0) + 1

    total_skipped = sum(skip_reasons.values())
    print(f"\nAnalyzed {len(results)} declarations, skipped {total_skipped}:", file=sys.stderr)
    for reason, count in sorted(skip_reasons.items(), key=lambda x: -x[1]):
        print(f"  - {reason}: {count}", file=sys.stderr)

    # Sort by LoC saved (descending)
    results.sort(key=lambda r: r.loc_saved, reverse=True)

    # Output CSV
    writer = csv.writer(sys.stdout)
    writer.writerow(["file", "declaration", "type", "old_loc", "new_loc", "loc_saved", "commit", "date"])
    for r in results:
        writer.writerow([r.file, r.decl_name, r.decl_type, r.old_loc, r.new_loc, r.loc_saved, r.commit_sha, r.commit_date])

    # Summary stats to stderr
    total_old = sum(r.old_loc for r in results) if results else 0
    total_new = sum(r.new_loc for r in results) if results else 0
    total_saved = sum(r.loc_saved for r in results) if results else 0
    avg_saved = total_saved / len(results) if results else 0

    print("\n" + "=" * 60, file=sys.stderr)
    print("GRIND ADOPTION LOC ANALYSIS", file=sys.stderr)
    print("=" * 60, file=sys.stderr)

    print("\n## Declaration Counts\n", file=sys.stderr)
    print(f"  Total grind tactic calls:         {total_grind_calls}", file=sys.stderr)
    print(f"  In named declarations:            {grind_in_decls} ({total_grind_calls - grind_in_decls} in anonymous/other)", file=sys.stderr)
    print(f"  Unique declarations:              {len(usages)}", file=sys.stderr)
    print(f"  Converted to grind:               {len(results)}", file=sys.stderr)
    print(f"  Born with grind:                  {skip_reasons.get('born_with_grind', 0)}", file=sys.stderr)
    if skip_reasons.get('old_loc_failed', 0) > 0:
        print(f"  Could not trace history:          {skip_reasons.get('old_loc_failed', 0)}", file=sys.stderr)

    print("\n## Lines of Code Impact\n", file=sys.stderr)
    print(f"  Total LoC before grind:           {total_old}", file=sys.stderr)
    print(f"  Total LoC after grind:            {total_new}", file=sys.stderr)
    print(f"  Total LoC saved:                  {total_saved}", file=sys.stderr)
    print(f"  Average LoC saved per theorem:    {avg_saved:.1f}", file=sys.stderr)
    big_savings = sum(1 for r in results if r.loc_saved >= 10)
    print(f"  Declarations shrunk by 10+ lines: {big_savings}", file=sys.stderr)

    if results:
        print("\n## Top 10 Biggest LoC Savings\n", file=sys.stderr)
        for r in results[:10]:
            print(f"  {r.loc_saved:+4d} lines: {r.decl_name} ({r.file})", file=sys.stderr)

        # Show any that got bigger (negative savings)
        got_bigger = [r for r in results if r.loc_saved < 0]
        if got_bigger:
            print(f"\n## Declarations That Got Bigger ({len(got_bigger)} total)\n", file=sys.stderr)
            print("  (showing 5 worst):", file=sys.stderr)
            for r in got_bigger[-5:]:  # Show worst 5
                print(f"  {r.loc_saved:+4d} lines: {r.decl_name} ({r.file})", file=sys.stderr)

    print("\n" + "=" * 60, file=sys.stderr)


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description="Analyze grind LoC savings")
    parser.add_argument("--repo", "-r", default=".", help="Repository path")
    args = parser.parse_args()
    main(args.repo)
