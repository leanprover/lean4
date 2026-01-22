#!/usr/bin/env python3

import argparse
import json
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

NAME = "build"
REPO = Path("..")
BENCH = REPO / "tests" / "bench-radar"
STAGE2 = REPO / "build" / "release" / "stage2"
OUT = REPO / "measurements.jsonl"


def save_result(metric: str, value: float, unit: str | None = None) -> None:
    data = {"metric": metric, "value": value}
    if unit is not None:
        data["unit"] = unit
    with open(OUT, "a") as f:
        f.write(f"{json.dumps(data)}\n")


def run(*command: str) -> None:
    result = subprocess.run(command)
    if result.returncode != 0:
        sys.exit(result.returncode)


def run_capture(*command: str) -> tuple[str, str]:
    result = subprocess.run(command, capture_output=True, encoding="utf-8")
    if result.returncode != 0:
        print(result.stdout, end="", file=sys.stdout)
        print(result.stderr, end="", file=sys.stderr)
        sys.exit(result.returncode)
    return result.stdout, result.stderr


def get_module(setup: Path) -> str:
    with open(setup) as f:
        return json.load(f)["name"]


def count_lines(module: str, path: Path) -> None:
    with open(path) as f:
        lines = sum(1 for _ in f)
    save_result(f"{NAME}/module/{module}//lines", lines)


def count_bytes(module: str, path: Path, suffix: str) -> None:
    try:
        bytes = path.with_suffix(suffix).stat().st_size
    except FileNotFoundError:
        return
    save_result(f"{NAME}/module/{module}//bytes {suffix}", bytes, "B")


def run_lean(module: str) -> None:
    stdout, stderr = run_capture(
        f"{BENCH}/measure.py",
        *("-t", f"{NAME}/module/{module}"),
        *("-o", f"{OUT}"),
        *("-m", "instructions"),
        *("-m", "cycles"),
        "--",
        f"{STAGE2}/bin/lean.wrapped",
        *("--profile", "-Dprofiler.threshold=9999999"),
        "--stat",
        *sys.argv[1:],
    )

    # Output of `lean --profile`
    # See timeit.cpp for the time format
    for line in stderr.splitlines():
        if match := re.fullmatch(r"\t(.*) ([\d.]+)(m?s)", line):
            name = match.group(1)
            seconds = float(match.group(2))
            if match.group(3) == "ms":
                seconds = seconds / 1000
            save_result(f"{NAME}/profile/{name}//wall-clock", seconds, "s")

    # Output of `lean --stat`
    stat = Counter[str]()
    for line in stdout.splitlines():
        if match := re.fullmatch(r"number of (imported .*):\s+(\d+)$", line):
            name = match.group(1)
            count = int(match.group(2))
            stat[name] += count
    for name, count in stat.items():
        if count > 0:
            if name.endswith("bytes"):
                save_result(f"{NAME}/stat/{name}//bytes", count, "B")
            else:
                save_result(f"{NAME}/stat/{name}//amount", count)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("lean", type=Path)
    parser.add_argument("--setup", type=Path)
    parser.add_argument("--i", "-i", type=Path)
    parser.add_argument("--o", "-o", type=Path)
    args, _ = parser.parse_known_args()

    lean: Path = args.lean
    setup: Path = args.setup
    ilean: Path | None = args.i
    olean: Path | None = args.o

    module = get_module(setup)

    count_lines(module, lean)
    run_lean(module)

    if ilean is not None:
        count_bytes(module, ilean, ".ilean")
    if olean is not None:
        count_bytes(module, olean, ".olean")
        count_bytes(module, olean, ".olean.server")
        count_bytes(module, olean, ".olean.private")


if __name__ == "__main__":
    main()
