#!/usr/bin/env python3

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

NAME = "stdlib"
REPO = Path("..")
BENCH = REPO / "tests" / "bench-radar"
STAGE2 = REPO / "build" / "release" / "stage2"
OUT = REPO / "radar.jsonl"


def save_result(metric: str, value: float, unit: str | None = None) -> None:
    data = {"metric": metric, "value": value}
    if unit is not None:
        data["unit"] = unit
    with open(OUT, "a+") as f:
        f.write(f"{json.dumps(data)}\n")


def run(*command: str) -> None:
    result = subprocess.run(command)
    if result.returncode != 0:
        sys.exit(result.returncode)


def run_stderr(*command: str) -> str:
    result = subprocess.run(command, capture_output=True, encoding="utf-8")
    if result.returncode != 0:
        print(result.stdout, end="", file=sys.stdout)
        print(result.stderr, end="", file=sys.stderr)
        sys.exit(result.returncode)
    return result.stderr


def get_module(setup: Path) -> str:
    with open(setup) as f:
        return json.load(f)["name"]


def count_lines(module: str, path: Path) -> None:
    with open(path) as f:
        lines = sum(1 for _ in f)
    save_result(f"{NAME}/module/{module}//lines", lines)


def run_lean(module: str) -> None:
    stderr = run_stderr(
        f"{BENCH}/measure.py",
        *("-t", f"{NAME}/module/{module}"),
        *("-o", f"{OUT}"),
        *("-m", "instructions"),
        "--",
        *(f"{STAGE2}/bin/lean.wrapped", "--profile", "-Dprofiler.threshold=9999999"),
        *sys.argv[1:],
    )

    for line in stderr.splitlines():
        # Output of `lean --profile`
        # See timeit.cpp for the time format
        if match := re.fullmatch(r"\t(.*) ([\d.]+)(m?s)", line):
            name = match.group(1)
            seconds = float(match.group(2))
            if match.group(3) == "ms":
                seconds = seconds / 1000
            save_result(f"{NAME}/profile/{name}//wall-clock", seconds, "s")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("lean", type=Path)
    parser.add_argument("--setup", type=Path)
    args, _ = parser.parse_known_args()

    lean: Path = args.lean
    setup: Path = args.setup

    module = get_module(setup)
    count_lines(module, lean)
    run_lean(module)


if __name__ == "__main__":
    main()
