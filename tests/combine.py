#!/usr/bin/env python3

import argparse
import json
import sys
from pathlib import Path
from typing import Any


def add_measurement(
    values: dict[str, float],
    units: dict[str, str | None],
    data: dict[str, Any],
) -> None:
    metric = data["metric"]
    values[metric] = values.get(metric, 0) + data["value"]
    units[metric] = data.get("unit")


def format_measurement(
    values: dict[str, float],
    units: dict[str, str | None],
    name: str,
) -> dict[str, Any]:
    value = values[name]
    unit = units.get(name)

    data: dict[str, Any] = {"metric": name, "value": value}
    if unit is not None:
        data["unit"] = unit

    return data


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Combine measurement files in the JSON Lines format, summing duplicated measurements like radar does.",
    )
    parser.add_argument(
        "input",
        nargs="*",
        default=[],
        help="input files to read measurements from. If none are specified, measurements are read from stdin.",
    )
    parser.add_argument(
        "-o",
        "--output",
        type=Path,
        help="output file to write measurements to. If not specified, the result is printed to stdout.",
    )
    args = parser.parse_args()

    inputs: list[Path] = args.input
    output: Path | None = args.output

    values: dict[str, float] = {}
    units: dict[str, str | None] = {}

    # Read measurements
    if inputs:
        for input in inputs:
            with open(input, "r") as f:
                for line in f:
                    add_measurement(values, units, json.loads(line))
    else:
        for line in sys.stdin:
            add_measurement(values, units, json.loads(line))

    # Write measurements
    if output:
        with open(output, "w") as f:
            for metric in sorted(values):
                f.write(f"{json.dumps(format_measurement(values, units, metric))}\n")
    else:
        for metric in sorted(values):
            print(json.dumps(format_measurement(values, units, metric)))


if __name__ == "__main__":
    main()
