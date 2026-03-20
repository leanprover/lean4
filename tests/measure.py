#!/usr/bin/env python3

import argparse
import json
import os
import resource
import subprocess
import sys
import tempfile
from argparse import Namespace
from dataclasses import dataclass
from pathlib import Path
from typing import Tuple


@dataclass
class PerfMetric:
    event: str
    factor: float = 1
    unit: str | None = None


@dataclass
class RusageMetric:
    name: str
    factor: float = 1
    unit: str | None = None


@dataclass
class Result:
    category: str
    value: float
    unit: str | None

    def fmt(self, topic: str) -> str:
        data = {"metric": f"{topic}//{self.category}", "value": self.value}
        if self.unit is not None:
            data["unit"] = self.unit
        return json.dumps(data)


PERF_METRICS = {
    "task-clock": PerfMetric("task-clock", factor=1e-9, unit="s"),
    "wall-clock": PerfMetric("duration_time", factor=1e-9, unit="s"),
    "instructions": PerfMetric("instructions"),
    "cycles": PerfMetric("cycles"),
}

PERF_UNITS = {
    "msec": 1e-3,
    "ns": 1e-9,
}

RUSAGE_METRICS = {
    "maxrss": RusageMetric("ru_maxrss", factor=1000, unit="B"),  # KiB on linux
}

ALL_METRICS = {**PERF_METRICS, **RUSAGE_METRICS}
DEFAULT_METRICS = set(ALL_METRICS.keys())


def resolve_metrics(metrics: set[str]) -> Tuple[set[str], set[str]]:
    perf = set()
    rusage = set()
    unknown = set()

    for metric in metrics:
        if metric in PERF_METRICS:
            perf.add(metric)
        elif metric in RUSAGE_METRICS:
            rusage.add(metric)
        else:
            unknown.add(metric)

    if unknown:
        raise SystemExit(f"unknown metrics: {', '.join(unknown)}")

    return perf, rusage


@dataclass
class PerfResult:
    value: float
    unit: str


type PerfResults = dict[str, PerfResult]


@dataclass
class MeasureResult:
    perf: PerfResults
    stdout: str
    stderr: str


def measure_perf(cmd: list[str], events: set[str], capture: bool) -> MeasureResult:
    with tempfile.NamedTemporaryFile() as tmp:
        env = os.environ.copy()
        env["LC_ALL"] = "C"  # or perf may output syntactically invalid JSON

        # On NixOS, perf effectively prepends /usr/bin to the PATH, but in this
        # test suite, we often use the PATH to specify the binaries under test.
        # Hence, we reset the PATH inside of perf using env.
        cmd = [
            *("perf", "stat", "-j", "-o", tmp.name),
            *(arg for event in sorted(events) for arg in ["-e", event]),
            "--",
            *("env", f"PATH={env['PATH']}"),
            *cmd,
        ]

        # Execute command
        result = subprocess.run(cmd, env=env, capture_output=capture, encoding="utf-8")
        if result.returncode != 0:
            sys.exit(result.returncode)

        # Collect results
        perf: PerfResults = {}
        for line in tmp:
            data = json.loads(line)
            if "event" in data and "counter-value" in data:
                perf[data["event"]] = PerfResult(
                    value=float(data["counter-value"]),
                    unit=data["unit"],
                )

        return MeasureResult(
            perf=perf,
            stdout=result.stdout or "",
            stderr=result.stderr or "",
        )


def get_perf_result(perf: PerfResults, metric: str) -> Result:
    info = PERF_METRICS[metric]
    if info.event in perf:
        result = perf[info.event]
    else:
        # Without the corresponding permissions,
        # we only get access to the userspace versions of the counters.
        result = perf[f"{info.event}:u"]

    value = result.value * PERF_UNITS.get(result.unit, info.factor)
    return Result(category=metric, value=value, unit=info.unit)


def get_rusage_result(rusage: resource.struct_rusage, metric: str) -> Result:
    info = RUSAGE_METRICS[metric]
    value = getattr(rusage, info.name) * info.factor
    return Result(category=metric, value=value, unit=info.unit)


def main(
    cmd: list[str],
    output: Path,
    topics: list[str],
    metrics: set[str],
    append: bool = True,
    capture: bool = False,
) -> tuple[str, str]:
    perf_metrics, rusage_metrics = resolve_metrics(metrics)
    perf_events = {PERF_METRICS[metric].event for metric in perf_metrics}

    measured = measure_perf(cmd, perf_events, capture=capture)
    perf = measured.perf
    rusage = resource.getrusage(resource.RUSAGE_CHILDREN)

    results = []
    for metric in perf_metrics:
        results.append(get_perf_result(perf, metric))
    for metric in rusage_metrics:
        results.append(get_rusage_result(rusage, metric))

    with open(output, "a" if append else "w") as f:
        for result in results:
            for topic in topics:
                f.write(f"{result.fmt(topic)}\n")

    return measured.stdout, measured.stderr


@dataclass
class Args(Namespace):
    topic: list[str]
    metric: list[str]
    default_metrics: bool
    output: Path
    append: bool
    cmd: str
    args: list[str]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Measure resource usage of a command using perf and rusage.",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument(
        "--topic",
        "-t",
        action="append",
        default=[],
        help="topic prefix for the metrics",
    )
    parser.add_argument(
        "--metric",
        "-m",
        action="append",
        default=[],
        help=f"metrics to measure. Can be specified multiple times. Available metrics: {', '.join(sorted(ALL_METRICS))}",
    )
    parser.add_argument(
        "--default-metrics",
        "-d",
        action="store_true",
        help=f"measure a default set of metrics: {', '.join(sorted(DEFAULT_METRICS))}",
    )
    parser.add_argument(
        "--output",
        "-o",
        type=Path,
        default=Path() / "measurements.jsonl",
        help="output file to write measurements to, in the JSON Lines format",
    )
    parser.add_argument(
        "--append",
        "-a",
        action="store_true",
        help="append to the output file instead of overwriting it",
    )
    parser.add_argument(
        "cmd",
        help="command to measure the resource usage of",
    )
    parser.add_argument(
        "args",
        nargs="*",
        default=[],
        help="arguments to pass to the command",
    )
    args = parser.parse_args(namespace=Args)

    metrics = set(args.metric)
    if args.default_metrics:
        metrics |= DEFAULT_METRICS

    main(
        cmd=[args.cmd] + args.args,
        output=args.output,
        topics=args.topic,
        metrics=metrics,
        append=args.append,
    )
