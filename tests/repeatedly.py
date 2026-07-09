#!/usr/bin/env python3

import argparse
import json
import subprocess
import sys
from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path

REPO = Path()
OUTFILE = REPO / "measurements.jsonl"
OUTFILE_TMP = REPO / "measurements_repeated_tmp.jsonl"


@dataclass
class Measurement:
    metric: str
    value: float
    unit: str | None

    @classmethod
    def from_json_str(cls, s: str) -> "Measurement":
        data = json.loads(s.strip())
        return cls(data["metric"], data["value"], data.get("unit"))

    def to_json_str(self) -> str:
        if self.unit is None:
            return json.dumps({"metric": self.metric, "value": self.value})
        return json.dumps(
            {"metric": self.metric, "value": self.value, "unit": self.unit}
        )


@contextmanager
def temporarily_move_outfile():
    if OUTFILE_TMP.exists():
        raise Exception(f"{OUTFILE_TMP} already exists")

    OUTFILE.touch()
    OUTFILE.rename(OUTFILE_TMP)
    try:
        yield
    finally:
        OUTFILE_TMP.rename(OUTFILE)


def read_measurements_from_outfile() -> list[Measurement]:
    measurements = []
    with open(OUTFILE, "r") as f:
        for line in f:
            measurements.append(Measurement.from_json_str(line))
    return measurements


def write_measurements_to_outfile(measurements: list[Measurement]) -> None:
    with open(OUTFILE, "a") as f:
        for measurement in measurements:
            f.write(f"{measurement.to_json_str()}\n")


def run_once(cmd: list[str]) -> list[Measurement]:
    with temporarily_move_outfile():
        proc = subprocess.run(cmd)
        if proc.returncode != 0:
            sys.exit(proc.returncode)

        return read_measurements_from_outfile()


def repeatedly(cmd: list[str], iterations: int) -> list[Measurement]:
    totals: dict[str, Measurement] = {}

    for i in range(iterations):
        for measurement in run_once(cmd):
            if existing := totals.get(measurement.metric):
                measurement.value += existing.value
            totals[measurement.metric] = measurement

    for measurement in totals.values():
        measurement.value /= iterations

    return list(totals.values())


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description=f"Repeatedly run a command, averaging the resulting measurements in {OUTFILE.name}.",
    )
    parser.add_argument(
        "-n",
        "--iterations",
        type=int,
        default=5,
        help="number of iterations",
    )
    parser.add_argument(
        "cmd",
        nargs="*",
        help="command to repeatedly run",
    )
    args = parser.parse_args()

    iterations: int = args.iterations
    cmd: list[str] = args.cmd

    measurements = repeatedly(cmd, iterations)
    write_measurements_to_outfile(measurements)
