# Lean 4 benchmark suite

This directory contains the new Lean 4 benchmark suite.
It is built around [radar](github.com/leanprover/radar)
and benchmark results can be viewed
on the [Lean FRO radar instance](https://radar.lean-lang.org/repos/lean4).

Benchmarks are organized into subdirectories.
Each benchmark directory must contain a script called `run` that executes the benchmark,
as well as any additional benchmark-specific required files.
Ideally, each benchmark directory also contains a `README.md` explaining the benchmark.

To execute the entire suite, run `tests/bench-radar/run` in the repo root.
To execute an individua benchmark, run `tests/bench-radar/<benchmark>/run` in the repo root.
All scripts output their measurements into the file `measurements.jsonl`.

Radar sums any duplicated measurements with matching metrics.
To post-process the `measurements.jsonl` file this way in-place,
run `tests/bench-radar/combine.py` in the repo root after executing the benchmark suite.

All scripts related to the new benchmark suite are contained in this directory.
The files at `tests/bench` belong to the old suite.
The `*.py` symlinks are only for convenience when editing the python scripts in VSCode,
so the python extensions (in particular pyrefly) treat it as a python file.
