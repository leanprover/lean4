import argparse
import json
import subprocess
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument("src", type=Path)
parser.add_argument("build", type=Path)
parser.add_argument("install", type=Path)
parser.add_argument("output", type=Path)
args = parser.parse_args()

src: Path = args.src
build: Path = args.build
install: Path = args.install
output: Path = args.output

build_temp = build / "lib" / "temp"
build_lean = build / "lib" / "lean"


def output_measurement(
    topic: str,
    category: str,
    value: float,
    unit: str | None = None,
) -> None:
    data = {"metric": f"{topic}//{category}", "value": value}
    if unit is not None:
        data["unit"] = unit
    with open(output, "a") as f:
        f.write(f"{json.dumps(data)}\n")


def measure_bytes_for_file(topic: str, path: Path, count: bool = True) -> None:
    bytes = path.stat().st_size

    output_measurement(topic, "bytes", bytes, "B")
    if count:
        output_measurement(topic, "files", 1)


def measure_bytes(topic: str, *paths: Path, count: bool = True) -> None:
    for path in paths:
        if path.is_file():
            measure_bytes_for_file(topic, path, count=count)


def measure_lines_for_file(topic: str, path: Path, count: bool = True) -> None:
    with open(path) as f:
        lines = sum(1 for _ in f)

    output_measurement(topic, "lines", lines)
    if count:
        output_measurement(topic, "files", 1)


def measure_lines(topic: str, *paths: Path, count: bool = True) -> None:
    for path in paths:
        if path.is_file():
            measure_lines_for_file(topic, path, count=count)


def measure_symbols_for_file(topic: str, path: Path, count: bool = True) -> None:
    result = subprocess.run(
        ["nm", "--extern-only", "--defined-only", path],
        capture_output=True,
        encoding="utf-8",
        check=True,
    )
    symbols = len(result.stdout.splitlines())

    output_measurement(topic, "dynamic symbols", symbols)
    if count:
        output_measurement(topic, "files", 1)


def measure_symbols(topic: str, *paths: Path, count: bool = True) -> None:
    for path in paths:
        if path.is_file():
            measure_symbols_for_file(topic, path, count=count)


# Make sure not to measure things that depend on other tests or benchmarks (like
# the tests/compile binary size) since you can't rely on the order the tests or
# benchmarks are executed in.

# Misc
measure_bytes("size/libleanshared.so", build_lean / "libleanshared.so", count=False)
measure_symbols("size/libleanshared.so", build_lean / "libleanshared.so", count=False)
measure_symbols("size/libLake_shared.so", build_lean / "libLake_shared.so", count=False)
measure_bytes("size/install", *install.rglob("*"))

# Stdlib
measure_lines("size/all/.c", *build_temp.rglob("*.c"))
measure_bytes("size/all/.ir", *build_lean.rglob("*.ir"))
measure_lines("size/all/.cpp", *src.rglob("*.cpp"))
measure_lines("size/all/.lean", *src.rglob("*.lean"))
measure_bytes("size/all/.ilean", *build_lean.rglob("*.ilean"))
measure_bytes("size/all/.olean", *build_lean.rglob("*.olean"))
measure_bytes("size/all/.olean.server", *build_lean.rglob("*.olean.server"))
measure_bytes("size/all/.olean.private", *build_lean.rglob("*.olean.private"))

# Init
measure_bytes("size/Init/.olean", *build_lean.glob("Init/**/*.olean"))
measure_bytes("size/Init/.olean.server", *build_lean.glob("Init/**/*.olean.server"))
measure_bytes("size/Init/.olean.private", *build_lean.glob("Init/**/*.olean.private"))
