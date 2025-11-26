#!/usr/bin/env python3

# Repeatedly run a command that outputs radar measurements on stdout or stderr.
# Average the results and re-emit them.

import argparse
import json
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

OUTPUT_PREFIX = "radar::measurement="


@dataclass
class Measurement:
    metric: str
    value: float
    unit: str | None

    def fmt(self) -> str:
        if self.unit is None:
            return json.dumps({"metric": self.metric, "value": self.value})
        return json.dumps(
            {"metric": self.metric, "value": self.value, "unit": self.unit}
        )


def parse_measurement(line: str) -> Measurement | None:
    start = line.find(OUTPUT_PREFIX)
    if start < 0:
        return
    data = json.loads(line[start + len(OUTPUT_PREFIX) :].strip())
    return Measurement(data["metric"], data["value"], data.get("unit"))


def run_once(cmd: list[str], quiet: bool) -> list[Measurement]:
    proc = subprocess.run(cmd, capture_output=True, encoding="utf-8")
    if proc.returncode != 0:
        print(proc.stdout, end="", file=sys.stdout)
        print(proc.stderr, end="", file=sys.stderr)
        sys.exit(proc.returncode)

    # We must not print the lines containing the measurements, else radar will collect them.
    measurements = []
    for line in proc.stdout.splitlines():
        if m := parse_measurement(line):
            measurements.append(m)
        elif not quiet:
            print(line, file=sys.stdout)
    for line in proc.stderr.splitlines():
        if m := parse_measurement(line):
            measurements.append(m)
        elif not quiet:
            print(line, file=sys.stderr)

    return measurements


def repeatedly(cmd: list[str], iterations: int, quiet: bool) -> list[Measurement]:
    totals: dict[str, Measurement] = {}

    for i in range(iterations):
        for measurement in run_once(cmd, quiet):
            if existing := totals.get(measurement.metric):
                measurement.value += existing.value
            totals[measurement.metric] = measurement

    for measurement in totals.values():
        measurement.value /= iterations

    return list(totals.values())


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("-n", "--iterations", type=int, default=5)
    parser.add_argument("-q", "--quiet", action="store_true")
    parser.add_argument("-o", "--output", type=Path)
    parser.add_argument("cmd", nargs="*")
    args = parser.parse_args()

    iterations: int = args.iterations
    quiet: bool = args.quiet
    output: Path | None = args.output
    cmd: list[str] = args.cmd

    measurements = repeatedly(cmd, iterations, quiet)

    if output:
        with open(output, "a+") as f:
            for result in measurements:
                f.write(f"{result.fmt()}\n")
    else:
        for result in measurements:
            print(f"{OUTPUT_PREFIX}{result.fmt()}")
