# Test suite

This directory contains the lean test and benchmark suite.
It is currently in the process of being migrated to the framework described in this file.
Some tests still use the previous framework,
which is partially documented in [testing.md](../doc/dev/testing.md).

The test suite consists of two types of directories: Test directories and test piles.

A **test directory** is a directory containing a `run_test` and/or a `run_bench` script.
It represents a single test or benchmark, depending on which script is present.
The run scripts are executed once with their working directory set to the test directory.

A **test pile** is also a directory containing a `run_test` and/or a `run_bench` script.
Here however, each file of a directory-specific extension (usually `.lean`) represents a single test or benchmark.
The run scripts are executed once for each test file with their working directory set to the pile directory.
Often, additional supplementary files are placed next to the test files and interpreted by the run scripts.

## Directory structure

Benchmarks belonging to the old framework are not included in this description.

- `bench`:
  A bunch of benchmarks and benchmarking related files,
  most of which are not part of the test suite.
  - `build`:
    A benchmark that builds the lean stdlib and measures the per-file performance.
  - `size`:
    A benchmark that measures the sizes of a few different kinds of files.
- `compile`:
  Tests that compile lean files and then execute the resulting binary, verifying the resulting output.
  They also run the same lean file through the interpreter.
- `compile_bench`:
  Benchmarks that compile lean files and measure the execution of the resulting binary,
  as well as optionally run the same lean file through the interpreter.
- `elab`:
  Tests that elaborate lean files without executing them, verifying the resulting output.
- `elab_fail`:
  Like `elab`, but expecting an exit code of 1 instead of 0.
- `elab_bench`:
  Like `elab`, but measuring the elaboration performance.
- `lake_bench`:
  Benchmark directories that measure lake performance.
- `misc`:
  A collection of miscellaneous small test scripts.
- `misc_bench`:
  A collection of miscellaneous small benchmark scripts.

## How to run the test suite?

Run all tests using

```sh
CTEST_PARALLEL_LEVEL="$(nproc)" CTEST_OUTPUT_ON_FAILURE=1 \
make -C build/release -j "$(nproc)" test
```

Or rerun only the failed tests using

```sh
CTEST_PARALLEL_LEVEL="$(nproc)" CTEST_OUTPUT_ON_FAILURE=1 \
make -C build/release -j "$(nproc)" test ARGS="--rerun-failed"
```

Run an individual test by `cd`-ing into its directory and then using

```sh
./run_test # in a test directory
./run_test testfile # in a test pile
```

## How to run the bench suite?

Run the full benchmark suite using

```sh
make -C build/release -j "$(nproc)" bench # produces tests/measurements.jsonl
```

It is split into two roughly equal parts so it can be split among the benchmark runner machines.
Run each individual part using

```sh
make -C build/release -j "$(nproc)" bench-part1 # produces tests/part1.measurements.jsonl
make -C build/release -j "$(nproc)" bench-part2 # produces tests/part2.measurements.jsonl
```

Make sure not to specify `-j "$(nproc)"` when running the bench suite manually inside `build/release/stage<n>`.

Run an individual benchmark by `cd`-ing into its directory and then using

```sh
./run_bench # in a test directory
./run_bench testfile # in a test pile
```

## How to write a test or benchmark?

If your test fits one of the existing test piles:

1. Add your test file to the test pile.
2. Document the test via doc comment inside the test file.
3. Execute the test as documented above (or run the entire test suite).
4. Run [`fix_expected.py`](fix_expected.py) to create an `.out.expected` or `.out.ignored` file for the test.
5. Run [`lint.py`](lint.py).

If your test should be part of one of the existing test directories:

1. Modify the test directory to include your test.
2. Document the test via comment or `README.md`, following the test directory's conventions.

Otherwise, create a new test directory or pile:

1. Decide on a place to put the new directory.
2. Write a `run_test` and/or `run_bench` script.
3. Add the directory to the [`CMakeLists.txt`](CMakeLists.txt) file,
   next to the other tests near the bottom.
4. Document the new directory in this readme file
   by updating the directory structure section above.
5. Optionally update [`lint.py`](lint.py) if it makes sense.

## How to fix existing tests after your change breaks them?

If the tests break because the expected output differs from the actual output,
don't blindly copy the produced output into the expected output file.
Instead, execute [`fix_expected.py`](fix_expected.py) (you need to have `meld` installed).
This script allows you to review the changes one-by-one.

If the test output is very brittle, either modify the test so the output becomes less brittle,
or ignore the output by removing `.out.expected`,
re-running `fix_expected.py` and choosing to ignore the output.
Brittle output that should usually be ignored are detailed compiler debug traces
or inherently nondeterministic things like multithreading.

Some test directories or test piles strip or modify certain flaky or nondeterministic outputs
(e.g. benchmark timings, reference manual URLs).

## How to write a test or bench run script?

Test and bench scripts must be named `run_test` and `run_bench` respectively.
They must be executable and start with the shebang `#!/usr/bin/env bash`.
Immediately afterwards, they must source `env_test.sh` or `env_bench.sh` respectively
using a relative path.

The `env_*.sh` files set some build related environment variables,
plus a set of test suite related environment variables
document at the top of [`CMakeLists.txt`](CMakeLists.txt).
The most notable ones are:

- `TEST_DIR`: Absolute path to the `tests` directory.
- `SCRIPT_DIR`: Absolute path to the `script` directory.
- `TEST_BENCH`: Set to `1` if we're currently executing a benchmark, unset otherwise.

Finally, the run script should source `"$TEST_DIR/util.sh"`,
which provides a few utility functions and also uses `set` to set sensible bash defaults.
See `util.sh` for the available utility functions.

The run scripts are always executed with their working directory set to their surrounding directory.
Inside a test pile, `run_test` and `run_bench` receive
a relative path to the file under test as their first (and only) argument.
Inside a test directory, they receive no arguments.

A test succeeds iff the `run_test` script exits with exit code 0.
A benchmark additionally must produce a measurements file:
Inside a test pile, `run_bench testfile` is expected to produce a `testfile.measurments.jsonl` file.
Inside a test directory, `run_bench` is expected to produce a `measurements.jsonl` file.

## The `elab*` test pile

These files are available to configure a test:

- `<file>.init.sh`:
  This file is sourced at the start of the run script.
  Configure the run script by setting bash variables here.

- `<file>.before.sh`:
  This file is executed before the test/benchmark.
  Create or set up temporary resources used by the test here.
  Usually, it is better to create temporary files or directories inside the test itself,
  so they're also available when opening the file in your editor.

- `<file>.after.sh`:
  This file is executed after the test/benchmark.
  Delete temporary resources used by the test here.

- `<file>.out.expected`:
  The test fails if its stdout and stderr doesn't match this file's contents.
  If this file isn't present, the test's output must be empty.

- `<file>.out.ignored`:
  Ignore the test's output entirely; don't compare it to `<file>.out.expected`.

- `<file>.exit.expected`:
  The test fails if its exit code doesn't match this file's contents.
  If this file isn't present, the pile's default exit code is used instead.

These bash variables (set via `<file>.init.sh`) are used by the run script:

- `TEST_LEAN_ARGS`:
  A bash array of additional arguments to the `lean` command.

## The `compile*` test pile

These files are available to configure a test:

- `<file>.(do|no)_(compile|interpret)`,
  `<file>.(do|no)_(compile|interpret)_(test|bench)`:
  Enable or disable the compiler or interpreter during testing or benchmarking.
  The more specific files take precedence over the more generic files.
  Instead of disabling the compiler during tests, consider reducing the problem size
  by passing different command line parameters via `<file>.init.sh`.

- `<file>.init.sh`:
  This file is sourced at the start of the run script.
  Configure the run script by setting bash variables here.

- `<file>.before.sh`:
  This file is executed before the test/benchmark.
  Create or set up temporary resources used by the test here.
  Usually, it is better to create temporary files or directories inside the test itself,
  so they're also available when opening the file in your editor.

- `<file>.after.sh`:
  This file is executed after the test/benchmark.
  Delete temporary resources used by the test here.

- `<file>.out.expected`:
  The test fails if its stdout and stderr doesn't match this file's contents.
  If this file isn't present, the test's output must be empty.

- `<file>.out.ignored`:
  Ignore the test's output entirely; don't compare it to `<file>.out.expected`.

- `<file>.exit.expected`:
  The test fails if its exit code doesn't match this file's contents.
  If this file isn't present, the test's exit code must be 0.

These bash variables (set via `<file>.init.sh`) are used by the run script:

- `TEST_LEAN_ARGS`:
  A bash array of additional arguments to the `lean` command used to compile the lean file.

- `TEST_LEANC_ARGS`:
  A bash array of additional arguments to the `leanc` command used to compile the c file.

- `TEST_LEANI_ARGS`:
  A bash array of additional arguments to the `lean --run <file>` command used to interpret the lean file.

- `TEST_ARGS`:
  A bash array of arguments to the compiled (or interpreted) program.
  Check `TEST_BENCH` if you want to specify more intense parameters for benchmarks.
