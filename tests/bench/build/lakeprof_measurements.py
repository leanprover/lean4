#!/usr/bin/env python3

# Derives the `build/lakeprof/*` measurements from `lakeprof report` and the
# existing contents of the measurements file. The results are appended back onto
# the measurements file.
#
# Must be run from the src dir so that lakeprof can collect the metadata it
# needs.

import argparse
import json
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path


def save_measurement(
    output: Path, metric: str, value: float, unit: str | None = None
) -> None:
    data = {"metric": metric, "value": value}
    if unit is not None:
        data["unit"] = unit
    with open(output, "a") as f:
        f.write(f"{json.dumps(data)}\n")


def load_instructions_per_module(output: Path) -> dict[str, float]:
    pattern = re.compile(r"build/module/(.*)//instructions")
    instructions: dict[str, float] = {}
    with open(output) as f:
        for line in f:
            data = json.loads(line)
            if match := pattern.fullmatch(data["metric"]):
                instructions[match.group(1)] = data["value"]
    return instructions


@dataclass
class Row:
    time: float
    time_frac: float
    cum_time: float
    cum_time_frac: float
    module: str


def lakeprof_report(*args: str) -> list[Row]:
    result = subprocess.run(
        ["lakeprof", "report", *args, "-j"], capture_output=True, encoding="utf-8"
    )
    if result.returncode != 0:
        print(result.stdout, end="", file=sys.stdout)
        print(result.stderr, end="", file=sys.stderr)
        sys.exit(result.returncode)
    return [Row(*row) for row in json.loads(result.stdout)]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("out", type=Path)
    args = parser.parse_args()
    out: Path = args.out

    instructions = load_instructions_per_module(out)

    for flag, name in [("-p", "longest build path"), ("-r", "longest rebuild path")]:
        rows = lakeprof_report(flag)

        # Total wall-clock time, as reported by lakeprof
        save_measurement(
            out, f"build/lakeprof/{name}//wall-clock", rows[-1].cum_time, "s"
        )

        # Total instructions, computed from lakeprof's modules and our own measurements
        total_instructions = sum(instructions.get(row.module, 0) for row in rows)
        save_measurement(
            out, f"build/lakeprof/{name}//instructions", total_instructions
        )


if __name__ == "__main__":
    main()
