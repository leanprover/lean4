#!/usr/bin/env python3

import argparse
import json
import subprocess
import sys
from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path


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
def temporarily_move_outfile(outfile: Path):
    outfile_tmp = outfile.with_name(outfile.name + ".repeatedly_tmp")
    if outfile_tmp.exists():
        raise Exception(f"{outfile_tmp} already exists")

    outfile.touch()
    outfile.rename(outfile_tmp)
    try:
        yield
    finally:
        outfile_tmp.rename(outfile)


def read_measurements_from_outfile(outfile: Path) -> list[Measurement]:
    measurements = []
    with open(outfile, "r") as f:
        for line in f:
            measurements.append(Measurement.from_json_str(line))
    return measurements


def write_measurements_to_outfile(
    outfile: Path, measurements: list[Measurement]
) -> None:
    with open(outfile, "a") as f:
        for measurement in measurements:
            f.write(f"{measurement.to_json_str()}\n")


def run_once(cmd: list[str], outfile: Path) -> list[Measurement]:
    with temporarily_move_outfile(outfile):
        proc = subprocess.run(cmd)
        if proc.returncode != 0:
            sys.exit(proc.returncode)

        return read_measurements_from_outfile(outfile)


def sum_by_metric(measurements: list[Measurement]) -> dict[str, Measurement]:
    totals: dict[str, Measurement] = {}
    for measurement in measurements:
        if existing := totals.get(measurement.metric):
            measurement.value += existing.value
        totals[measurement.metric] = measurement
    return totals


def repeatedly(
    cmd: list[str],
    iterations: int,
    outfile: Path,
    drop_highest: int = 0,
    drop_lowest: int = 0,
) -> list[Measurement]:
    by_metric: dict[str, list[Measurement]] = {}

    for i in range(iterations):
        for metric, measurement in sum_by_metric(run_once(cmd, outfile)).items():
            by_metric.setdefault(metric, []).append(measurement)

    if drop_highest + drop_lowest >= iterations:
        raise ValueError(
            f"drop_highest ({drop_highest}) + drop_lowest ({drop_lowest}) must be "
            f"less than the number of iterations ({iterations})"
        )

    results = []
    for metric, measurements in by_metric.items():
        if drop_highest or drop_lowest:
            measurements.sort(key=lambda m: m.value)
            measurements = measurements[drop_lowest : len(measurements) - drop_highest]
        if not measurements:
            continue
        unit = measurements[0].unit
        value = sum(m.value for m in measurements) / len(measurements)
        results.append(Measurement(metric, value, unit))

    return results


class Args:
    iterations: int
    drop_highest: int
    drop_lowest: int
    outfile: Path
    cmd: str
    args: list[str]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Repeatedly run a command, averaging the measurements it writes.",
    )
    parser.add_argument(
        "-n",
        "--iterations",
        type=int,
        default=5,
        help="number of iterations",
    )
    parser.add_argument(
        "-H",
        "--drop-highest",
        type=int,
        default=0,
        help="drop the n highest values of each metric before averaging",
    )
    parser.add_argument(
        "-L",
        "--drop-lowest",
        type=int,
        default=0,
        help="drop the n lowest values of each metric before averaging",
    )
    parser.add_argument(
        "-o",
        "--outfile",
        type=Path,
        default=Path("measurements.jsonl"),
        help="measurements file the command under test writes to",
    )
    parser.add_argument(
        "cmd",
        help="command to repeatedly run",
    )
    parser.add_argument(
        "args",
        nargs="*",
        default=[],
        help="arguments to pass to the command",
    )
    args = parser.parse_args(namespace=Args())

    measurements = repeatedly(
        [args.cmd] + args.args,
        args.iterations,
        args.outfile,
        args.drop_highest,
        args.drop_lowest,
    )
    write_measurements_to_outfile(args.outfile, measurements)
