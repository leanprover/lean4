#!/usr/bin/env python3

import glob as glob_
import os
import re
import subprocess
import sys
from pathlib import Path

# Run in repo root
os.chdir(Path(__file__).parent.parent)


# We only inspect files tracked by git, and those should never be modified by
# tests, so this should safely run in parallel with other tests.
TRACKED_LIST = sorted(
    name
    for name in subprocess.run(
        ["git", "ls-files", "-z"],
        capture_output=True,
        text=True,
        check=True,
    ).stdout.split("\0")
    if name
)
TRACKED_SET = {Path(name) for name in TRACKED_LIST}


def glob(*patterns: str):
    # `Path.full_match` recompiles the pattern on every call, which makes this
    # script a lot slower than it needs to be.
    compiled = [
        re.compile(glob_.translate(pattern, recursive=True, include_hidden=True))
        for pattern in patterns
    ]

    for name in TRACKED_LIST:
        if any(regex.match(name) for regex in compiled):
            yield Path(name)


ERROR = False


def nag(reason: str, path: Path, fatal: bool = True) -> None:
    print(f"{reason:>16}: {path}")
    if fatal:
        global ERROR
        ERROR = True


# Files and directories that will no longer work.

for file in glob(
    "**/*.exit.expected",
    "**/*.expected.out",
    "**/*.expected.ret",
    "**/*.no_interpreter",
    "**/run_bench",
    "**/run_test",
    "tests/speedcenter.exec.velcom.yaml",
):
    nag("removed file", file)

for file in glob(
    "tests/bench-radar/*",
    "tests/bench/cbv/*",
    "tests/bench/inundation/*",
    "tests/compiler/*",
    "tests/lean/docparse/*",
    "tests/lean/interactive/*",
    "tests/lean/run/*",
    "tests/lean/server/*",
    "tests/lean/trust0/*",
    "tests/plugin/*",
    "tests/lean/*.lean",
    "tests/lean/*.expected.out",
    "tests/lean/*.expected.ret",
):
    nag("removed dir", file)


# Files that use the old naming convention in the new directories.

for dir in (
    "doc/examples",
    "tests/compile",
    "tests/compile_bench",
    "tests/docparse",
    "tests/elab",
    "tests/elab_bench",
    "tests/elab_fail",
    "tests/misc",
    "tests/misc_bench",
    "tests/server",
    "tests/server_interactive",
):
    for file in glob(
        f"{dir}/*.no_interpreter",
        f"{dir}/*.expected.out",
        f"{dir}/*.expected.ret",
    ):
        nag("old suffix", file)


# Files that expect a corresponding base file

for pattern, drop in (
    ("**/*.no_test", 1),
    ("**/*.no_bench", 1),
    ("**/*.do_compile", 1),
    ("**/*.do_compile", 1),
    ("**/*.do_compile_test", 1),
    ("**/*.do_compile_bench", 1),
    ("**/*.do_interpret", 1),
    ("**/*.do_interpret_test", 1),
    ("**/*.do_interpret_bench", 1),
    ("**/*.no_compile", 1),
    ("**/*.no_compile", 1),
    ("**/*.no_compile_test", 1),
    ("**/*.no_compile_bench", 1),
    ("**/*.no_interpret", 1),
    ("**/*.no_interpret_test", 1),
    ("**/*.no_interpret_bench", 1),
    ("**/*.init.sh", 2),
    ("**/*.before.sh", 2),
    ("**/*.after.sh", 2),
    ("**/*.out.expected", 2),
    ("**/*.out.ignored", 2),
):
    for file in glob(pattern):
        basefile = file
        for _ in range(drop):
            basefile = basefile.with_suffix("")
        if basefile in TRACKED_SET:
            continue
        if basefile == Path(
            "tests/pkg/leanchecker/LeanCheckerTests/PrivateConflictC.lean.fresh"
        ):
            continue
        nag("missing base", file)


# Files that shouldn't be empty

for file in glob(
    "**/*.init.sh",
    "**/*.before.sh",
    "**/*.after.sh",
):
    if file.read_text().strip():
        continue
    nag("empty", file)

# We need to be a bit more peculiar about whitespace here
for file in glob("**/*.out.expected"):
    if file.read_bytes():
        continue
    nag("empty", file)


# .out.ignored and .out.expected collision

for file in glob("**/*.out.ignored"):
    if file.with_suffix(".expected") in TRACKED_SET:
        nag("has .expected", file)


# .no_test but .out.expected/.out.ignored

for file in glob("**/*.no_test"):
    if file.with_suffix(".out.expected") in TRACKED_SET:
        nag("has .no_test", file)
    if file.with_suffix(".out.ignored") in TRACKED_SET:
        nag("has .no_test", file)


# Special rules for certain directories

for file in glob(
    "tests/compile_bench/*.no_bench",
    "tests/elab_bench/*.no_bench",
    "tests/misc_bench/*.no_bench",
):
    nag("forbidden", file)


# File confusion by case insensitive filesystems

seen: set[str] = set()
for file in glob("**/*"):
    path = str(file).lower()
    if path in seen:
        nag("case sensitive", file)
    seen.add(path)


if ERROR:
    sys.exit(1)
