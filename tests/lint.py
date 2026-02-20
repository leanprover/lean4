#!/usr/bin/env python

import os
import sys
from pathlib import Path

# Run in repo root
os.chdir(Path(__file__).parent.parent)


ERROR = False


def nag(reason: str, path: Path, fatal: bool = True) -> None:
    print(f"{reason:>16}: {path}")
    if fatal:
        global ERROR
        ERROR = True


# Directories that should no longer be used but still work for now.

for dir in (
    "tests/compiler",
    "tests/lean",
    "tests/lean/run",
):
    for glob in (
        f"{dir}/*.lean",
        f"{dir}/*.expected.out",
        f"{dir}/*.expected.ret",
    ):
        for file in Path().glob(glob):
            nag("deprecated dir", file, fatal=False)


# Files and directories that will no longer work.

for file in Path().glob("tests/speedcenter.exec.velcom.yaml"):
    nag("removed file", file)

for file in Path().glob("tests/bench-radar/*"):
    nag("removed dir", file)

for dir in (
    "tests/bench/cbv",
    "tests/lean/trust0",
):
    for glob in (
        f"{dir}/*.lean",
        f"{dir}/*.expected.out",
        f"{dir}/*.expected.ret",
    ):
        for file in Path().glob(glob):
            nag("removed dir", file)


# Files that use the old naming convention in the new directories.

for dir in (
    "tests/compile",
    "tests/compile_bench",
    "tests/elab",
    "tests/elab_bench",
    "tests/elab_fail",
):
    for glob in (
        f"{dir}/*.no_interpreter",
        f"{dir}/*.expected.out",
        f"{dir}/*.expected.ret",
    ):
        for file in Path().glob(glob):
            nag("old suffix", file)


# Files that expect a corresponding base file

for glob, drop in (
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
    ("**/*.exit.expected", 2),
    # Old naming convention
    ("**/*.no_interpreter", 1),
    ("**/*.expected.out", 2),
    ("**/*.expected.ret", 2),
):
    for file in Path().glob(glob):
        basefile = file
        for _ in range(drop):
            basefile = basefile.with_suffix("")
        if basefile.exists():
            continue
        if basefile == Path(
            "tests/pkg/leanchecker/LeanCheckerTests/PrivateConflictC.lean.fresh"
        ):
            continue
        nag("missing base", file)


# Files that shouldn't be empty

for glob in (
    "**/*.init.sh",
    "**/*.before.sh",
    "**/*.after.sh",
    "**/*.exit.expected",
):
    for file in Path().glob(glob):
        if file.read_text().strip():
            continue
        nag("empty", file)

# We need to be a bit more peculiar about whitespace here
for file in Path().glob("**/*.out.expected"):
    if file.read_bytes():
        continue
    nag("empty", file)


# .out.ignored and .out.expected collision

for file in Path().glob("**/*.out.ignored"):
    if file.with_suffix(".expected").exists():
        nag("has .expected", file)


# .no_test but .out.expected/.out.ignored

for file in Path().glob("**/*.no_test"):
    if file.with_suffix(".out.expected").exists():
        nag("has .no_test", file)
    if file.with_suffix(".out.ignored").exists():
        nag("has .no_test", file)


# Special rules for certain directories

for glob in (
    "tests/elab/*.exit.expected",
    "tests/elab_bench/*.no_bench",
    "tests/compile_bench/*.no_bench",
):
    for file in Path().glob(glob):
        nag("forbidden", file)

for file in Path().glob("tests/elab_fail/*.exit.expected"):
    if file.read_text().strip() == "0":
        nag("must be != 0", file)


# Run scripts sourcing incorrectly

for file in Path().glob("**/run_test"):
    if file.is_symlink():
        continue
    text = file.read_text()
    if "env_test.sh" not in text:
        nag("no env_test.sh", file)
    if "env_bench.sh" in text:
        nag("has env_bench.sh", file)

for file in Path().glob("**/run_bench"):
    if file.is_symlink():
        continue
    text = file.read_text()
    if "env_bench.sh" not in text:
        nag("no env_bench.sh", file)
    if "env_test.sh" in text:
        nag("has env_test.sh", file)


if ERROR:
    sys.exit(1)
