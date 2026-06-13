#!/usr/bin/env python3
"""scan-commits.py — Walk a git range and classify commits by backend-path touches.

Emits per-commit JSON reports and a deterministic manifest.json.
Uses only the Python standard library.
"""

from __future__ import annotations

import argparse
import os
import hashlib
import json
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable

# ---------------------------------------------------------------------------
# Backend path prefixes (in order of specificity)
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

# Subsystem names used in counts_per_subsystem
SUBSYSTEM_MAP = {
    "src/runtime/": "runtime",
    "src/Lean/Compiler/IR/": "compiler_ir",
    "src/Lean/Compiler/LCNF/": "compiler_lcnf",
    "src/include/lean/": "include_lean",
    "src/shell/": "shell",
    "src/Init/": "init",
    "src/library/compiler/": "library_compiler",
}

# Zig target mapping for backend paths
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


def classify_subsystem(path: str) -> str | None:
    """Return the subsystem key for a backend path, or None."""
    for prefix, subsys in SUBSYSTEM_MAP.items():
        if path.startswith(prefix):
            return subsys
    return None


def classify_subsystems(changes: list[dict]) -> dict[str, int]:
    """Count how many changes fall into each subsystem."""
    counts: dict[str, int] = {}
    for ch in changes:
        subsys = classify_subsystem(ch["path"])
        if subsys:
            counts[subsys] = counts.get(subsys, 0) + 1
    return counts


# ---------------------------------------------------------------------------
# Git helpers
# ---------------------------------------------------------------------------

def git_log_commits(repo: str, since: str, to: str) -> list[dict]:
    """Return list of commit dicts with sha, subject, author, date."""
    if since == to:
        return []
    fmt = "%H%x00%s%x00%an%x00%ad%x00"
    cmd = [
        "git", "-C", repo,
        "log", f"{since}..{to}",
        "--reverse",
        "--format=" + fmt,
        "--date=short",
    ]
    out = subprocess.run(cmd, capture_output=True, text=True, check=True)
    commits: list[dict] = []
    for block in out.stdout.strip().split("\x00\n"):
        parts = block.split("\x00")
        if len(parts) >= 4:
            commits.append({
                "sha": parts[0].strip(),
                "subject": parts[1].strip(),
                "author": parts[2].strip(),
                "date": parts[3].strip(),
            })
    if should_prepend_since_commit(since, to) and is_ancestor(repo, since, to):
        commits.insert(0, git_show_commit(repo, since))
    return commits


def should_prepend_since_commit(since: str, to: str) -> bool:
    """Return True when the lower bound should be treated as inclusive."""
    if since == to:
        return False
    if since == "HEAD":
        return False
    return not any(marker in since for marker in ("^", "~", ":", ".."))


def is_ancestor(repo: str, ancestor: str, descendant: str) -> bool:
    """Return True if *ancestor* is an ancestor of *descendant*."""
    cmd = ["git", "-C", repo, "merge-base", "--is-ancestor", ancestor, descendant]
    result = subprocess.run(cmd, capture_output=True, text=True)
    return result.returncode == 0


def git_show_commit(repo: str, rev: str) -> dict:
    """Return commit metadata for a single revision."""
    fmt = "%H%x00%s%x00%an%x00%ad"
    cmd = [
        "git", "-C", repo,
        "show", "-s", f"--format={fmt}",
        "--date=short",
        rev,
    ]
    out = subprocess.run(cmd, capture_output=True, text=True, check=True)
    sha, subject, author, date = out.stdout.strip().split("\x00")
    return {
        "sha": sha.strip(),
        "subject": subject.strip(),
        "author": author.strip(),
        "date": date.strip(),
    }


def git_diff_tree(repo: str, sha: str) -> str:
    """Return raw diff-tree output for a commit (parent..sha)."""
    # Use --no-renames first, then detect renames separately for robustness
    cmd = [
        "git", "-C", repo,
        "diff-tree", "--no-commit-id", "--name-status", "-r", "-M", sha,
    ]
    out = subprocess.run(cmd, capture_output=True, text=True, check=True)
    return out.stdout


# ---------------------------------------------------------------------------
# Diff parsing
# ---------------------------------------------------------------------------

def parse_diff(diff_text: str) -> list[dict]:
    """Parse git diff-tree --name-status output into change dicts.

    Handles:
      A\tpath
      M\tpath
      D\tpath
      R100\told\tnew
    """
    changes: list[dict] = []
    for line in diff_text.strip().splitlines():
        line = line.strip()
        if not line:
            continue
        parts = line.split("\t")
        status = parts[0][0]  # A, M, D, R
        if status == "R":
            if len(parts) >= 3:
                changes.append({
                    "path": parts[2],
                    "status": "R",
                    "old_path": parts[1],
                })
        elif status in ("A", "M", "D"):
            changes.append({
                "path": parts[1],
                "status": status,
            })
    return changes


# ---------------------------------------------------------------------------
# Report building
# ---------------------------------------------------------------------------

def build_report(
    sha: str,
    short_sha: str,
    subject: str,
    author: str,
    date: str,
    changes: list[dict],
    max_kb: int = 10,
) -> dict:
    """Build a per-commit report dict, capping JSON size at ~max_kb."""
    backend_changes = []
    for ch in changes:
        if is_backend_change(ch["path"]):
            entry = {
                "path": ch["path"],
                "status": ch["status"],
                "zig_target": zig_target_for(ch["path"]),
            }
            if ch.get("old_path"):
                entry["old_path"] = ch["old_path"]
            backend_changes.append(entry)

    # Sort deterministically
    backend_changes.sort(key=lambda x: x["path"])
    zig_target = {
        change["path"]: change["zig_target"]
        for change in backend_changes
    }

    report = {
        "sha": sha,
        "short_sha": short_sha,
        "subject": subject,
        "author": author,
        "date": date,
        "needs_port": len(backend_changes) > 0,
        "backend_changes": backend_changes,
        "zig_target": dict(sorted(zig_target.items())),
    }

    # Footprint cap: if oversized, truncate change list and mark
    raw = json.dumps(report, sort_keys=True, indent=2)
    max_bytes = max_kb * 1024
    if len(raw.encode("utf-8")) > max_bytes and len(backend_changes) > 0:
        # Binary search for how many changes fit
        lo, hi = 0, len(backend_changes)
        while lo < hi:
            mid = (lo + hi + 1) // 2
            truncated_changes = backend_changes[:mid]
            test_report = dict(report)
            test_report["backend_changes"] = truncated_changes
            test_report["zig_target"] = {
                change["path"]: change["zig_target"]
                for change in truncated_changes
            }
            test_report["truncated"] = True
            test_raw = json.dumps(test_report, sort_keys=True, indent=2)
            if len(test_raw.encode("utf-8")) <= max_bytes:
                lo = mid
            else:
                hi = mid - 1
        report["backend_changes"] = backend_changes[:lo]
        report["zig_target"] = {
            change["path"]: change["zig_target"]
            for change in report["backend_changes"]
        }
        report["truncated"] = True

    return report


def write_report(report: dict, out_dir: Path) -> None:
    """Write a per-commit report as deterministic JSON."""
    short = report["short_sha"]
    path = out_dir / f"{short}.json"
    payload = json.dumps(report, sort_keys=True, indent=2)
    path.write_text(payload, encoding="utf-8")


# ---------------------------------------------------------------------------
# Manifest building
# ---------------------------------------------------------------------------

def compute_content_hash(reports: Iterable[dict]) -> str:
    """SHA-256 over sorted report JSON payloads."""
    payloads = []
    for report in sorted(reports, key=lambda item: item["short_sha"]):
        payloads.append(json.dumps(report, sort_keys=True, separators=(",", ":")))
    data = "\n".join(payloads).encode("utf-8")
    return hashlib.sha256(data).hexdigest()


def build_manifest(
    commits: list[dict],
    reports: list[dict],
) -> dict:
    """Build the top-level manifest from processed commits."""
    total = len(commits)
    backend_touching = sum(1 for r in reports if r["needs_port"])

    counts_per_year: dict[str, int] = {}
    counts_per_subsystem: dict[str, int] = {}

    for r in reports:
        year = r["date"][:4]
        counts_per_year[year] = counts_per_year.get(year, 0) + 1
        for ch in r["backend_changes"]:
            subsys = classify_subsystem(ch["path"])
            if subsys:
                counts_per_subsystem[subsys] = counts_per_subsystem.get(subsys, 0) + 1

    manifest = {
        "total_commits": total,
        "backend_touching_commits": backend_touching,
        "counts_per_year": dict(sorted(counts_per_year.items())),
        "counts_per_subsystem": dict(sorted(counts_per_subsystem.items())),
        "content_hash": compute_content_hash(reports),
    }
    return manifest


def build_scan_info(
    total_commits: int,
    backend_touching_commits: int,
    start_time: float,
) -> dict:
    """Build volatile scan metadata kept separate from deterministic manifest."""
    return {
        "total_commits": total_commits,
        "backend_touching_commits": backend_touching_commits,
        "scan_timestamp_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "scan_duration_seconds": round(time.time() - start_time, 3),
    }


def write_json(path: Path, payload: dict) -> None:
    """Write JSON with deterministic formatting."""
    path.write_text(
        json.dumps(payload, sort_keys=True, indent=2),
        encoding="utf-8",
    )


# ---------------------------------------------------------------------------
# Main scan
# ---------------------------------------------------------------------------

def scan_range(
    repo: str,
    since: str,
    to: str,
    out_dir: Path,
    max_kb: int = 10,
) -> dict:
    """Scan a commit range and write reports + manifest.json.

    Returns the manifest dict.
    """
    start_time = time.time()
    out_dir.mkdir(parents=True, exist_ok=True)
    sync_dir = out_dir.parent

    commits = git_log_commits(repo, since, to)
    reports: list[dict] = []

    for c in commits:
        short_sha = c["sha"][:10]
        diff_text = git_diff_tree(repo, c["sha"])
        changes = parse_diff(diff_text)
        report = build_report(
            sha=c["sha"],
            short_sha=short_sha,
            subject=c["subject"],
            author=c["author"],
            date=c["date"],
            changes=changes,
            max_kb=max_kb,
        )
        write_report(report, out_dir)
        reports.append(report)

    manifest = build_manifest(commits, reports)
    write_json(sync_dir / "manifest.json", manifest)
    write_json(out_dir / "manifest.json", manifest)
    scan_info = build_scan_info(
        total_commits=manifest["total_commits"],
        backend_touching_commits=manifest["backend_touching_commits"],
        start_time=start_time,
    )
    write_json(sync_dir / "scan-info.json", scan_info)
    return manifest


# ---------------------------------------------------------------------------
# Check mode
# ---------------------------------------------------------------------------

def check_mode(repo: str, since: str, to: str, out_dir: Path) -> int:
    """Verify that every commit in the range has a corresponding report."""
    commits = git_log_commits(repo, since, to)
    missing = 0
    sync_dir = out_dir.parent
    if not (sync_dir / "manifest.json").exists():
        print(f"MISSING: {sync_dir / 'manifest.json'}", file=sys.stderr)
        missing += 1
    for c in commits:
        short = c["sha"][:10]
        if not (out_dir / f"{short}.json").exists():
            missing += 1
            print(f"MISSING: {short} {c['subject']}", file=sys.stderr)
    if missing:
        print(f"Check failed: {missing}/{len(commits)} reports missing.", file=sys.stderr)
        return 1
    print(f"Check passed: {len(commits)} reports present.")
    return 0


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Walk a git range and classify commits by backend-path touches.",
    )
    parser.add_argument(
        "--since",
        default="0556412f8d",
        help="Starting commit (default: 0556412f8d)",
    )
    parser.add_argument(
        "--to",
        default="HEAD",
        help="Ending commit (default: HEAD)",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="Verify reports exist for the range without rewriting.",
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
        help="Output directory for reports and manifest (default: REPO/zig-backend/sync/reports)",
    )
    args = parser.parse_args(argv)

    repo = args.repo
    out_dir = Path(args.out_dir) if args.out_dir else Path(repo) / "zig-backend" / "sync" / "reports"

    if args.check:
        return check_mode(repo, args.since, args.to, out_dir)

    manifest = scan_range(repo, args.since, args.to, out_dir)
    print(
        f"Scanned {manifest['total_commits']} commits, "
        f"{manifest['backend_touching_commits']} backend-touching. "
        f"Manifest hash: {manifest['content_hash'][:16]}..."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
