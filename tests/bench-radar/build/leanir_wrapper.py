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


def count_bytes(module: str, path: Path, suffix: str) -> None:
    try:
        bytes = path.with_suffix(suffix).stat().st_size
    except FileNotFoundError:
        return
    save_result(f"{NAME}/module/ir/{module}//bytes {suffix}", bytes, "B")


def run_leanir(module: str) -> None:
    stdout, stderr = run_capture(
        f"{BENCH}/measure.py",
        *("-t", f"{NAME}/module/ir/{module}"),
        *("-o", f"{OUT}"),
        *("-m", "instructions"),
        *("-m", "cycles"),
        "--",
        f"{STAGE2}/bin/leanir.wrapped",
        *sys.argv[2:],
        *("-Dprofiler=true", "-Dprofiler.threshold=9999999"),
    )

    # Output of `leanir -Dprofiler=true`
    # See timeit.cpp for the time format
    for line in stderr.splitlines():
        if match := re.fullmatch(r"\t(.*) ([\d.]+)(m?s)", line):
            name = match.group(1)
            seconds = float(match.group(2))
            if match.group(3) == "ms":
                seconds = seconds / 1000
            save_result(f"{NAME}/profile/ir/{name}//wall-clock", seconds, "s")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("setup", type=Path)
    parser.add_argument("ir", type=Path)
    parser.add_argument("c", type=Path)
    args, _ = parser.parse_known_args()

    module = get_module(args.setup)

    run_leanir(module)

    count_bytes(module, args.ir, ".ir")
    count_bytes(module, args.c, ".c")

if __name__ == "__main__":
    main()
