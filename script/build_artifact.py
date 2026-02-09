#!/usr/bin/env python3
"""
build_artifact.py: Download pre-built CI artifacts for a Lean commit.

Usage:
    build_artifact.py                     # Download artifact for current HEAD
    build_artifact.py --sha abc1234       # Download artifact for specific commit
    build_artifact.py --clear-cache       # Clear artifact cache

This script downloads pre-built binaries from GitHub Actions CI runs,
which is much faster than building from source (~30s vs 2-5min).

Artifacts are cached in ~/.cache/lean_build_artifact/ for reuse.
"""

import argparse
import json
import os
import platform
import shutil
import subprocess
import sys
import urllib.request
import urllib.error
from pathlib import Path
from typing import Optional

# Constants
GITHUB_API_BASE = "https://api.github.com"
LEAN4_REPO = "leanprover/lean4"

# CI artifact cache
CACHE_DIR = Path.home() / '.cache' / 'lean_build_artifact'
ARTIFACT_CACHE = CACHE_DIR

# Sentinel value indicating CI failed (don't bother building locally)
CI_FAILED = object()

# ANSI colors for terminal output
class Colors:
    RED = '\033[91m'
    GREEN = '\033[92m'
    YELLOW = '\033[93m'
    BLUE = '\033[94m'
    BOLD = '\033[1m'
    RESET = '\033[0m'

def color(text: str, c: str) -> str:
    """Apply color to text if stdout is a tty."""
    if sys.stdout.isatty():
        return f"{c}{text}{Colors.RESET}"
    return text

def error(msg: str) -> None:
    """Print error message and exit."""
    print(color(f"Error: {msg}", Colors.RED), file=sys.stderr)
    sys.exit(1)

def warn(msg: str) -> None:
    """Print warning message."""
    print(color(f"Warning: {msg}", Colors.YELLOW), file=sys.stderr)

def info(msg: str) -> None:
    """Print info message."""
    print(color(msg, Colors.BLUE), file=sys.stderr)

def success(msg: str) -> None:
    """Print success message."""
    print(color(msg, Colors.GREEN), file=sys.stderr)

# -----------------------------------------------------------------------------
# Platform detection
# -----------------------------------------------------------------------------

def get_artifact_name() -> Optional[str]:
    """Get CI artifact name for current platform."""
    system = platform.system()
    machine = platform.machine()

    if system == 'Darwin':
        if machine == 'arm64':
            return 'build-macOS aarch64'
        return 'build-macOS'  # Intel
    elif system == 'Linux':
        if machine == 'aarch64':
            return 'build-Linux aarch64'
        return 'build-Linux release'
    # Windows not supported for CI artifact download
    return None

# -----------------------------------------------------------------------------
# GitHub API helpers
# -----------------------------------------------------------------------------

_github_token_warning_shown = False

def get_github_token() -> Optional[str]:
    """Get GitHub token from environment or gh CLI."""
    global _github_token_warning_shown

    # Check environment variable first
    token = os.environ.get('GITHUB_TOKEN')
    if token:
        return token

    # Try to get token from gh CLI
    try:
        result = subprocess.run(
            ['gh', 'auth', 'token'],
            capture_output=True,
            text=True,
            timeout=5
        )
        if result.returncode == 0 and result.stdout.strip():
            return result.stdout.strip()
    except (FileNotFoundError, subprocess.TimeoutExpired):
        pass

    # Warn once if no token available
    if not _github_token_warning_shown:
        _github_token_warning_shown = True
        warn("No GitHub authentication found. API rate limits may apply.")
        warn("Run 'gh auth login' or set GITHUB_TOKEN to avoid rate limiting.")

    return None

def github_api_request(url: str) -> dict:
    """Make a GitHub API request and return JSON response."""
    headers = {
        'Accept': 'application/vnd.github.v3+json',
        'User-Agent': 'build-artifact'
    }

    token = get_github_token()
    if token:
        headers['Authorization'] = f'token {token}'

    req = urllib.request.Request(url, headers=headers)
    try:
        with urllib.request.urlopen(req, timeout=30) as response:
            return json.loads(response.read().decode())
    except urllib.error.HTTPError as e:
        if e.code == 403:
            error(f"GitHub API rate limit exceeded. Set GITHUB_TOKEN environment variable to increase limit.")
        elif e.code == 404:
            error(f"GitHub resource not found: {url}")
        else:
            error(f"GitHub API error: {e.code} {e.reason}")
    except urllib.error.URLError as e:
        error(f"Network error accessing GitHub API: {e.reason}")

# -----------------------------------------------------------------------------
# CI artifact cache functions
# -----------------------------------------------------------------------------

def get_cache_path(sha: str) -> Path:
    """Get cache directory for a commit's artifact."""
    return ARTIFACT_CACHE / sha[:12]

def is_cached(sha: str) -> bool:
    """Check if artifact for this commit is already cached and valid."""
    cache_path = get_cache_path(sha)
    return cache_path.exists() and (cache_path / 'bin' / 'lean').exists()

def check_zstd_support() -> bool:
    """Check if tar supports zstd compression."""
    try:
        result = subprocess.run(
            ['tar', '--zstd', '--version'],
            capture_output=True,
            timeout=5
        )
        return result.returncode == 0
    except (subprocess.TimeoutExpired, FileNotFoundError):
        return False

def check_gh_available() -> bool:
    """Check if gh CLI is available and authenticated."""
    try:
        result = subprocess.run(
            ['gh', 'auth', 'status'],
            capture_output=True,
            timeout=10
        )
        return result.returncode == 0
    except (subprocess.TimeoutExpired, FileNotFoundError):
        return False

def download_ci_artifact(sha: str, quiet: bool = False):
    """
    Try to download CI artifact for a commit.
    Returns:
      - Path to extracted toolchain directory if available
      - CI_FAILED sentinel if CI run failed (don't bother building locally)
      - None if no artifact available but local build might work
    """
    # Check cache first
    if is_cached(sha):
        return get_cache_path(sha)

    artifact_name = get_artifact_name()
    if artifact_name is None:
        return None  # Unsupported platform

    cache_path = get_cache_path(sha)

    try:
        # Query for CI workflow run for this commit, including status
        # Note: Query parameters must be in the URL for GET requests
        result = subprocess.run(
            ['gh', 'api', f'repos/{LEAN4_REPO}/actions/runs?head_sha={sha}&per_page=100',
             '--jq', r'.workflow_runs[] | select(.name == "CI") | "\(.id) \(.conclusion // "null")"'],
            capture_output=True,
            text=True,
            timeout=30
        )
        if result.returncode != 0 or not result.stdout.strip():
            return None  # No CI run found (old commit?)

        # Parse "run_id conclusion" format
        line = result.stdout.strip().split('\n')[0]
        parts = line.split(' ', 1)
        run_id = parts[0]
        conclusion = parts[1] if len(parts) > 1 else "null"

        # Check if the desired artifact exists for this run
        result = subprocess.run(
            ['gh', 'api', f'repos/{LEAN4_REPO}/actions/runs/{run_id}/artifacts',
             '--jq', f'.artifacts[] | select(.name == "{artifact_name}") | .id'],
            capture_output=True,
            text=True,
            timeout=30
        )
        if result.returncode != 0 or not result.stdout.strip():
            # No artifact available
            # If CI failed and no artifact, the build itself likely failed - skip
            if conclusion == "failure":
                return CI_FAILED
            # Otherwise (in progress, expired, etc.) - fall back to local build
            return None

        # Download artifact
        cache_path.mkdir(parents=True, exist_ok=True)
        if not quiet:
            print("downloading CI artifact... ", end='', flush=True)

        result = subprocess.run(
            ['gh', 'run', 'download', run_id,
             '-n', artifact_name,
             '-R', LEAN4_REPO,
             '-D', str(cache_path)],
            capture_output=True,
            text=True,
            timeout=600  # 10 minutes for large downloads
        )

        if result.returncode != 0:
            shutil.rmtree(cache_path, ignore_errors=True)
            return None

        # Extract tar.zst - find the file (name varies by platform/version)
        tar_files = list(cache_path.glob('*.tar.zst'))
        if not tar_files:
            shutil.rmtree(cache_path, ignore_errors=True)
            return None

        tar_file = tar_files[0]
        if not quiet:
            print("extracting... ", end='', flush=True)

        result = subprocess.run(
            ['tar', '--zstd', '-xf', tar_file.name],
            cwd=cache_path,
            capture_output=True,
            timeout=300
        )

        if result.returncode != 0:
            shutil.rmtree(cache_path, ignore_errors=True)
            return None

        # Move contents up from lean-VERSION-PLATFORM/ to cache_path/
        # The extracted directory name varies (e.g., lean-4.15.0-linux, lean-4.15.0-darwin_aarch64)
        extracted_dirs = [d for d in cache_path.iterdir() if d.is_dir() and d.name.startswith('lean-')]
        if extracted_dirs:
            extracted = extracted_dirs[0]
            for item in extracted.iterdir():
                dest = cache_path / item.name
                if dest.exists():
                    if dest.is_dir():
                        shutil.rmtree(dest)
                    else:
                        dest.unlink()
                shutil.move(str(item), str(cache_path / item.name))
            extracted.rmdir()

        # Clean up tar file
        tar_file.unlink()

        # Verify the extraction worked
        if not (cache_path / 'bin' / 'lean').exists():
            shutil.rmtree(cache_path, ignore_errors=True)
            return None

        return cache_path

    except (subprocess.TimeoutExpired, FileNotFoundError):
        shutil.rmtree(cache_path, ignore_errors=True)
        return None

# -----------------------------------------------------------------------------
# Git helpers
# -----------------------------------------------------------------------------

def get_current_commit() -> str:
    """Get the current git HEAD commit SHA."""
    try:
        result = subprocess.run(
            ['git', 'rev-parse', 'HEAD'],
            capture_output=True,
            text=True,
            timeout=5
        )
        if result.returncode == 0:
            return result.stdout.strip()
        error(f"Failed to get current commit: {result.stderr.strip()}")
    except subprocess.TimeoutExpired:
        error("Timeout getting current commit")
    except FileNotFoundError:
        error("git not found")

def resolve_sha(short_sha: str) -> str:
    """Resolve a (possibly short) SHA to full 40-character SHA using git rev-parse."""
    if len(short_sha) == 40:
        return short_sha
    try:
        result = subprocess.run(
            ['git', 'rev-parse', short_sha],
            capture_output=True,
            text=True,
            timeout=5
        )
        if result.returncode == 0:
            full_sha = result.stdout.strip()
            if len(full_sha) == 40:
                return full_sha
        error(f"Cannot resolve SHA '{short_sha}': {result.stderr.strip() or 'not found in repository'}")
    except subprocess.TimeoutExpired:
        error(f"Timeout resolving SHA '{short_sha}'")
    except FileNotFoundError:
        error("git not found - required for SHA resolution")

# -----------------------------------------------------------------------------
# Main
# -----------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description='Download pre-built CI artifacts for a Lean commit.',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
This script downloads pre-built binaries from GitHub Actions CI runs,
which is much faster than building from source (~30s vs 2-5min).

Artifacts are cached in ~/.cache/lean_build_artifact/ for reuse.

Examples:
  build_artifact.py                   # Download for current HEAD
  build_artifact.py --sha abc1234     # Download for specific commit
  build_artifact.py --clear-cache     # Clear cache to free disk space
"""
    )

    parser.add_argument('--sha', metavar='SHA',
                        help='Commit SHA to download artifact for (default: current HEAD)')
    parser.add_argument('--clear-cache', action='store_true',
                        help='Clear artifact cache and exit')
    parser.add_argument('--quiet', '-q', action='store_true',
                        help='Suppress progress messages (still prints result path)')

    args = parser.parse_args()

    # Handle cache clearing
    if args.clear_cache:
        if ARTIFACT_CACHE.exists():
            size = sum(f.stat().st_size for f in ARTIFACT_CACHE.rglob('*') if f.is_file())
            shutil.rmtree(ARTIFACT_CACHE)
            info(f"Cleared cache at {ARTIFACT_CACHE} ({size / 1024 / 1024:.1f} MB)")
        else:
            info(f"Cache directory does not exist: {ARTIFACT_CACHE}")
        return

    # Get commit SHA
    if args.sha:
        sha = resolve_sha(args.sha)
    else:
        sha = get_current_commit()

    if not args.quiet:
        info(f"Commit: {sha[:12]}")

    # Check prerequisites
    if not check_gh_available():
        error("gh CLI not available or not authenticated. Run 'gh auth login' first.")

    if not check_zstd_support():
        error("tar does not support zstd compression. Install zstd or a newer tar.")

    artifact_name = get_artifact_name()
    if artifact_name is None:
        error(f"No CI artifacts available for this platform ({platform.system()} {platform.machine()})")

    if not args.quiet:
        info(f"Platform: {artifact_name}")

    # Check cache
    if is_cached(sha):
        path = get_cache_path(sha)
        if not args.quiet:
            success("Using cached artifact")
        print(path)
        return

    # Download artifact
    result = download_ci_artifact(sha, quiet=args.quiet)

    if result is CI_FAILED:
        if not args.quiet:
            print()  # End the "downloading..." line
        error(f"CI build failed for commit {sha[:12]}")
    elif result is None:
        if not args.quiet:
            print()  # End the "downloading..." line
        error(f"No CI artifact available for commit {sha[:12]}")
    else:
        if not args.quiet:
            print(color("done", Colors.GREEN))
        print(result)

if __name__ == '__main__':
    main()
