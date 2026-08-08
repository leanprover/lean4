---
name: lean4-benchmarks
description: Working with the Lean4 benchmark system. Use when creating, running, or analyzing benchmarks, or when working in tests/elab_bench/ or tests/compile_bench/.
---

# Lean4 Benchmarks

## Two Benchmark Piles

- **`tests/elab_bench/`** -- elaboration benchmarks. Each `.lean` file is elaborated by `lean` and measured.
- **`tests/compile_bench/`** -- compile+run benchmarks. Each `.lean` is compiled to C, then native binary, then execution is measured.

New `.lean` files are auto-registered via the glob in `tests/CMakeLists.txt`.

## Running

```bash
# Full suite → tests/measurements.jsonl
make -C build/release -j$(nproc) bench

# Single benchmark manually (test sizes, fast):
tests/with_stage1_test_env.sh tests/elab_bench/run_bench.sh foo.lean

# Single benchmark at real sizes (sets TEST_BENCH=1):
tests/with_stage1_bench_env.sh tests/elab_bench/run_bench.sh foo.lean
```

## Variable-Size Benchmarks

`TEST_BENCH` env var: unset in tests, set to `1` in benchmarks. Two mechanisms:

**compile_bench** -- create `foo.lean.init.sh` sidecar:
```bash
TEST_ARGS=( 10 )
if [[ -n $TEST_BENCH ]]; then
  TEST_ARGS=( 100 )
fi
```

**elab_bench** -- check in Lean:
```lean
let bench := (← IO.getEnv "TEST_BENCH") == some "1"
let sizes := if bench then [6, 10, 14, 18, 20] else [6]
```

## JSONL Measurement Format

Metrics use the format `topic//category`:
```json
{"metric": "elab/foo//wall-clock", "value": 0.5, "unit": "s"}
{"metric": "elab/foo//instructions", "value": 1200000000}
```

Default categories from `measure.py` (wraps `perf stat` + `rusage`):
`wall-clock`, `task-clock`, `instructions`, `cycles`, `maxrss`.

## Custom Metrics from Lean

Print to stdout in this exact format:
```
measurement: compress 0.123 s
measurement: parse 0.045 s
```
`extract_measurements` in `util.sh` converts these to JSONL automatically.

## combine.py

Merges JSONL files. **Sums duplicate metrics** -- if you re-run without deleting
the `.measurements.jsonl` file, values double. (CMake targets handle this via `remove -f`.)

```bash
python3 tests/combine.py -o combined.jsonl file1.jsonl file2.jsonl
```

## Scaling Analysis

No built-in tool. Write a custom script per `tests/bench/mergeSort/bench.py`:
run at multiple sizes, fit curves with scipy, plot with matplotlib.
