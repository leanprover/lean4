#!/usr/bin/env python3
"""replay.py — Generate markdown replay summaries for backend commits.

Given a SHA, inspects C++/Lean backend files at that commit (read-only via
`git show`), computes diff vs the previous backend-touching commit, and emits
a markdown summary at replays/<short-sha>.md.

CLI:
    replay.py <sha>
    replay.py --range <sha1>..<sha2>
    replay.py --help
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Iterable

# ---------------------------------------------------------------------------
# Backend path prefixes (must match scan-commits.py)
# ---------------------------------------------------------------------------
BACKEND_PREFIXES = [
    "src/runtime/",
    "src/Lean/Compiler/IR/",
    "src/Lean/Compiler/LCNF/",
    "src/include/lean/",
    "src/shell/",
    "src/Init/",
    "src/library/compiler/",
]

ZIG_TARGET_MAP = {
    "src/runtime/": "zig-backend/src/runtime/",
    "src/Lean/Compiler/IR/": "zig-backend/src/lean/compiler/ir/",
    "src/Lean/Compiler/LCNF/": "zig-backend/src/lean/compiler/lcnf/",
    "src/include/lean/": "zig-backend/include/lean/",
    "src/shell/": "zig-backend/src/shell/",
    "src/Init/": "zig-backend/src/init/",
    "src/library/compiler/": "zig-backend/src/library/compiler/",
}


def zig_target_for(path: str) -> str:
    """Map a backend source path to its proposed Zig target path."""
    for prefix, target in ZIG_TARGET_MAP.items():
        if path.startswith(prefix):
            return target + path[len(prefix):]
    return "zig-backend/unknown/" + path


def is_backend_change(path: str) -> bool:
    """Return True if *path* is under any backend prefix."""
    return any(path.startswith(p) for p in BACKEND_PREFIXES)


# ---------------------------------------------------------------------------
# Git helpers
# ---------------------------------------------------------------------------

def git_show_file(repo: str, sha: str, path: str) -> str:
    """Return the contents of *path* at *sha* via `git show`."""
    cmd = ["git", "-C", repo, "show", f"{sha}:{path}"]
    result = subprocess.run(cmd, capture_output=True, text=True)
    if result.returncode != 0:
        return ""
    return result.stdout


def git_diff_commits(repo: str, old_sha: str, new_sha: str, path: str | None = None) -> str:
    """Return unified diff between old_sha and new_sha, optionally filtered to path."""
    cmd = ["git", "-C", repo, "diff", "--no-color", "-U3", old_sha, new_sha]
    if path:
        cmd.append("--")
        cmd.append(path)
    result = subprocess.run(cmd, capture_output=True, text=True, check=True)
    return result.stdout


def get_commit_metadata(repo: str, sha: str) -> dict:
    """Return dict with sha, short_sha, subject, author, date."""
    fmt = "%H%x00%s%x00%an%x00%ad%x00"
    cmd = [
        "git", "-C", repo,
        "log", "-1", sha,
        "--format=" + fmt,
        "--date=short",
    ]
    out = subprocess.run(cmd, capture_output=True, text=True, check=True)
    parts = out.stdout.strip().split("\x00")
    return {
        "sha": parts[0].strip(),
        "short_sha": parts[0].strip()[:10],
        "subject": parts[1].strip(),
        "author": parts[2].strip(),
        "date": parts[3].strip(),
    }


def find_previous_backend_commit(repo: str, sha: str) -> str | None:
    """Walk backwards from *sha* to find the most recent commit that touches backend paths."""
    # First, get the parent of sha
    cmd = ["git", "-C", repo, "log", "--format=%H", "-1", f"{sha}^"]
    result = subprocess.run(cmd, capture_output=True, text=True, check=True)
    parent = result.stdout.strip()
    if not parent:
        return None

    # Search backwards for the most recent commit that touches backend paths
    cmd = [
        "git", "-C", repo,
        "log", f"{parent}", "--format=%H",
        "--reverse",
    ]
    # Actually, better approach: find all backend-touching commits up to parent,
    # then pick the latest one.
    cmd = [
        "git", "-C", repo,
        "log", f"{parent}", "--format=%H",
    ]
    out = subprocess.run(cmd, capture_output=True, text=True, check=True)
    all_shas = [line.strip() for line in out.stdout.strip().splitlines() if line.strip()]

    # Check each commit (from newest to oldest) for backend touches
    for candidate in reversed(all_shas):
        diff_tree = subprocess.run(
            ["git", "-C", repo, "diff-tree", "--no-commit-id", "--name-only", "-r", candidate],
            capture_output=True, text=True, check=True,
        )
        paths = [p.strip() for p in diff_tree.stdout.strip().splitlines() if p.strip()]
        if any(is_backend_change(p) for p in paths):
            return candidate

    # Fallback: return the parent itself if nothing found
    return parent if parent else None


def get_changed_files(repo: str, old_sha: str, new_sha: str) -> list[dict]:
    """Return list of change dicts {path, status, old_path?} between two commits."""
    cmd = [
        "git", "-C", repo, "diff", "--name-status", old_sha, new_sha,
    ]
    out = subprocess.run(cmd, capture_output=True, text=True, check=True)
    changes: list[dict] = []
    for line in out.stdout.strip().splitlines():
        line = line.strip()
        if not line:
            continue
        parts = line.split("\t")
        status = parts[0][0]  # A, M, D, R
        if status == "R":
            if len(parts) >= 3:
                changes.append({"path": parts[2], "status": "R", "old_path": parts[1]})
        elif status in ("A", "M", "D"):
            changes.append({"path": parts[1], "status": status})
    return changes


# ---------------------------------------------------------------------------
# Non-trivial change detection
# ---------------------------------------------------------------------------

def detect_non_trivial_changes(diff_lines: list[str]) -> list[str]:
    """Scan diff lines and flag struct defs, new exported symbols, removed symbols."""
    notes: list[str] = []
    for line in diff_lines:
        stripped = line.lstrip("+- ")
        if line.startswith("+"):
            if re.search(r"\bstruct\s+\w+\s*\{", stripped):
                notes.append(f"New struct definition: {stripped.strip()}")
            if "LEAN_EXPORT" in stripped:
                # Extract symbol name roughly
                m = re.search(r"LEAN_EXPORT\s+.*?\b(\w+)\s*\(", stripped)
                if m:
                    notes.append(f"New exported symbol: {m.group(1)}")
                else:
                    notes.append(f"New exported symbol: {stripped.strip()}")
        elif line.startswith("-"):
            if "LEAN_EXPORT" in stripped:
                m = re.search(r"LEAN_EXPORT\s+.*?\b(\w+)\s*\(", stripped)
                if m:
                    notes.append(f"Removed exported symbol: {m.group(1)}")
                else:
                    notes.append(f"Removed exported symbol: {stripped.strip()}")
            if re.search(r"\bstruct\s+\w+\s*\{", stripped):
                notes.append(f"Removed struct definition: {stripped.strip()}")
    return notes


def summarize_diff(diff_text: str, max_lines: int = 20) -> str:
    """Return a brief summary of the diff (first few hunk headers + context)."""
    lines = diff_text.splitlines()
    summary_lines: list[str] = []
    for line in lines:
        if line.startswith("@@") or line.startswith("diff --git") or line.startswith("index "):
            summary_lines.append(line)
        if len(summary_lines) >= max_lines:
            summary_lines.append("...")
            break
    if not summary_lines:
        # Show first few changed lines
        for line in lines:
            if line.startswith("+") or line.startswith("-"):
                summary_lines.append(line)
            if len(summary_lines) >= max_lines:
                summary_lines.append("...")
                break
    return "\n".join(summary_lines) if summary_lines else "(no diff available)"


# ---------------------------------------------------------------------------
# Markdown generation
# ---------------------------------------------------------------------------

def build_markdown(
    meta: dict,
    prev_sha: str | None,
    changes: list[dict],
    repo: str,
) -> str:
    """Build the full markdown replay document."""
    lines: list[str] = []
    lines.append(f"# Replay: {meta['short_sha']} — {meta['subject']}")
    lines.append("")
    lines.append("## Commit Metadata")
    lines.append("")
    lines.append(f"- **SHA:** `{meta['sha']}`")
    lines.append(f"- **Short SHA:** `{meta['short_sha']}`")
    lines.append(f"- **Author:** {meta['author']}")
    lines.append(f"- **Date:** {meta['date']}")
    lines.append(f"- **Subject:** {meta['subject']}")
    if prev_sha:
        lines.append(f"- **Previous Backend Commit:** `{prev_sha}`")
    else:
        lines.append("- **Previous Backend Commit:** *(none — this is the first backend commit)*")
    lines.append("")

    # Files Changed
    lines.append("## Files Changed")
    lines.append("")
    lines.append("| Status | Path | Zig Target |")
    lines.append("|--------|------|------------|")
    backend_changes = [c for c in changes if is_backend_change(c["path"])]
    if backend_changes:
        for ch in sorted(backend_changes, key=lambda x: x["path"]):
            status = ch["status"]
            path = ch["path"]
            target = zig_target_for(path)
            if ch.get("old_path"):
                path = f"{ch['old_path']} → {path}"
            lines.append(f"| {status} | `{path}` | `{target}` |")
    else:
        lines.append("| — | *(no backend files touched)* | — |")
    lines.append("")

    # Per-file diff summaries
    lines.append("## Diff Summaries")
    lines.append("")
    if backend_changes and prev_sha:
        for ch in sorted(backend_changes, key=lambda x: x["path"]):
            path = ch["path"]
            lines.append(f"### `{path}`")
            lines.append("")
            try:
                diff = git_diff_commits(repo, prev_sha, meta["sha"], path)
            except subprocess.CalledProcessError:
                diff = ""
            if diff:
                lines.append("```diff")
                lines.append(summarize_diff(diff, max_lines=15))
                lines.append("```")
            else:
                lines.append("*(diff unavailable — file may be new or deleted)*")
            lines.append("")
    else:
        lines.append("*(no backend changes to summarize)*")
        lines.append("")

    # Translation Notes
    lines.append("## Translation Notes")
    lines.append("")
    all_notes: list[str] = []
    if backend_changes and prev_sha:
        for ch in backend_changes:
            path = ch["path"]
            try:
                diff = git_diff_commits(repo, prev_sha, meta["sha"], path)
            except subprocess.CalledProcessError:
                diff = ""
            if diff:
                diff_lines = diff.splitlines()
                notes = detect_non_trivial_changes(diff_lines)
                for note in notes:
                    all_notes.append(f"- `{path}`: {note}")
    if all_notes:
        for note in all_notes:
            lines.append(note)
    else:
        lines.append("*(no non-trivial changes detected)*")
    lines.append("")

    # Footer
    lines.append("---")
    lines.append(f"*Generated by replay.py for commit {meta['short_sha']}*")
    lines.append("")

    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Main replay
# ---------------------------------------------------------------------------

def replay_commit(repo: str, sha: str, out_dir: Path) -> Path:
    """Generate a markdown replay for a single commit."""
    meta = get_commit_metadata(repo, sha)
    prev_sha = find_previous_backend_commit(repo, meta["sha"])
    if prev_sha:
        changes = get_changed_files(repo, prev_sha, meta["sha"])
    else:
        # First backend commit: show all files added
        diff_tree = subprocess.run(
            ["git", "-C", repo, "diff-tree", "--no-commit-id", "--name-status", "-r", "-M", meta["sha"]],
            capture_output=True, text=True, check=True,
        )
        changes = []
        for line in diff_tree.stdout.strip().splitlines():
            line = line.strip()
            if not line:
                continue
            parts = line.split("\t")
            status = parts[0][0]
            if status == "R" and len(parts) >= 3:
                changes.append({"path": parts[2], "status": "R", "old_path": parts[1]})
            elif status in ("A", "M", "D"):
                changes.append({"path": parts[1], "status": status})

    md = build_markdown(meta, prev_sha, changes, repo)
    out_path = out_dir / f"{meta['short_sha']}.md"
    out_path.write_text(md, encoding="utf-8")
    return out_path


def replay_range(repo: str, range_spec: str, out_dir: Path) -> list[Path]:
    """Replay all backend-touching commits in a range like 'sha1..sha2'."""
    parts = range_spec.split("..")
    if len(parts) != 2:
        raise ValueError(f"Invalid range spec: {range_spec!r} (expected sha1..sha2)")
    since, to = parts[0], parts[1]

    # Find all commits in the range (inclusive of both ends)
    cmd = [
        "git", "-C", repo,
        "log", f"{since}..{to}", "--format=%H", "--reverse",
    ]
    out = subprocess.run(cmd, capture_output=True, text=True, check=True)
    shas = [line.strip() for line in out.stdout.strip().splitlines() if line.strip()]
    # Also include the 'to' commit itself if it is backend-touching
    # (git log A..B excludes A but includes B; for A==B the range is empty)
    if since == to and to not in shas:
        shas.append(to)

    paths: list[Path] = []
    for sha in shas:
        # Only replay if the commit touches backend paths
        diff_tree = subprocess.run(
            ["git", "-C", repo, "diff-tree", "--no-commit-id", "--name-only", "-r", sha],
            capture_output=True, text=True, check=True,
        )
        touched = [p.strip() for p in diff_tree.stdout.strip().splitlines() if p.strip()]
        if any(is_backend_change(p) for p in touched):
            p = replay_commit(repo, sha, out_dir)
            paths.append(p)

    return paths


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Generate markdown replay summaries for backend commits.",
    )
    parser.add_argument(
        "sha",
        nargs="?",
        help="Commit SHA to replay",
    )
    parser.add_argument(
        "--range",
        dest="range_spec",
        help="Replay all backend commits in a range (e.g. sha1..sha2)",
    )
    parser.add_argument(
        "--repo",
        default=os.environ.get(
            "LEAN4_DIR", str(Path(__file__).resolve().parents[2])
        ),
        help="Path to the lean4 git repository "
        "(default: $LEAN4_DIR or the grandparent of this script)",
    )
    parser.add_argument(
        "--out-dir",
        default=None,
        help="Output directory for markdown files (default: REPO/zig-backend/replays)",
    )
    args = parser.parse_args(argv)

    repo = args.repo
    out_dir = Path(args.out_dir) if args.out_dir else Path(repo) / "zig-backend" / "replays"
    out_dir.mkdir(parents=True, exist_ok=True)

    if args.range_spec:
        paths = replay_range(repo, args.range_spec, out_dir)
        print(f"Replayed {len(paths)} backend commits to {out_dir}")
        return 0

    if not args.sha:
        parser.print_help()
        return 1

    out_path = replay_commit(repo, args.sha, out_dir)
    print(f"Replay written to {out_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
