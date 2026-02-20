# Test suite

- How to use?
- How to write (good) tests?
- How to write (good) benchmarks?
- How to fix tests?

- How the test suite is structured
- How the test suite works

- `.out.ignored`
- output normalization
- printing measurements

**Warning:** This document doesn't describe the test/bench suite as-is,
but instead the planned end result.
It also doesn't yet incorporate parts of [the old test suite docs](../doc/dev/testing.md).

## Using the test and bench suites

After [building Lean](../doc/make/index.md), run all tests using

```sh
CTEST_PARALLEL_LEVEL=$(nproc) CTEST_OUTPUT_ON_FAILURE=1 make -C build/release test
# Only rerun failed tests:
CTEST_PARALLEL_LEVEL=$(nproc) CTEST_OUTPUT_ON_FAILURE=1 make -C build/release test ARGS="--rerun-failed"
```

Run the benchmark suite using

```sh
make -C build/release bench # produces tests/measurements.jsonl
# Run halves separately:
make -C build/release bench-part1 # produces tests/part1.measurements.jsonl
make -C build/release bench-part2 # produces tests/part2.measurements.jsonl
```

The benchmark suite is split into two parts
so it can be split roughly evenly between two benchmark runner machines.
The `test`, `bench`, `bench-part1`, and `bench-part2` targets
are also available for every stage except stage0.

To run an individual test or benchmark, `cd` into the corresponding directory and run

```sh
# In a test dir:
./run_test
./run_bench
# In a test pile:
./run_test the_test_file.lean
./run_bench the_test_file.lean
```

If tests start failing due to mismatched output after a change,
the `fix_expected.py` script uses `meld` to let you quickly fix the `*.expected` files.
First, execute the full test suite, the run `fix_expected.py` (the working directory doesn't matter).
Blindly copying the produced output without review is usually not a good idea.

To lint the test and benchmark files, run `lint.py` (the working directory doesn't matter).

## Test suite structure

The test piles and test directores are defined in `tests/CMakeLists.txt`.
Most of them are located in the `tests` directory.

<!-- TODO parts of the "old" test suite -->

- `tests/compile`, `tests/compile_bench`: See _Compile tests_ below.
- `tests/elab`, `tests/elab_fail`, `tests/elab_bench`: See _Elab tests_ below.
- `tests/misc`, `tests/misc_bench`: A collection of individual test and bench scripts.

## Test piles and test directories

A test directory is a directory representing a single test and/or benchmark.
A test pile is a directory representing one test and/or benchmark
per contained file of a specific type (usually `.lean` files).

Both types of directory function similarly.
If they contain a `run_test` script, they are part of the test suite.
If they contain a `run_bench` script, they are part of the test suite.
The run scripts are executed with their working directory set to the directory.
If they fail with nonzero exit code, the test or benchmark fails.
In a test pile, the run script receives the (relative) path to the file under test as its first and only argument.

When `run_bench` is executed in a test directory, it should produce a `measurements.jsonl` file.
When it is executed in a test pile, it should produce a `<file>.measurements.jsonl` file.

To disable tests or benchmarks for a single file `<file>` in a pile,
create an empty file `<file>.no_test` or `<file>.no_bench` respectively.
These files are recognized by cmake, so you may need to re-configure the stage you're in
using `cmake -C build/release stage<n>-configure` if cmake didn't do so automatically.

In a test pile, if a test requires additional files or directories,
their names should be prefixed with the test file name.
For example, if a test called `list_dir.lean` requires a directory,
you could call the directory `list_dir.lean.dir`, but _not_ `list_dir.dir` or `example`.
This convention prevents tests from interacting with each other,
which is especially important since they are usually run in a random order or in parallel.

To add a new test pile or test directory, edit `tests/CMakeLists.txt`
and use the `add_test_pile` or `add_test_dir` functions.
Their usage is documented in the same file.

## Test and bench run scripts

As described in the section on test piles and test directories,
the `run_test` and `run_bench` scripts are used to drive the individual tests and benchmarks.
They are expected to be idempotent, ideally even without `*.before.sh` and `*.after.sh`.

The very first thing a run script should do
is to source `tests/env_test.sh` or `tests/env_bench.sh` respectively
using a path relative to the file's working directory.
The env file then sets the appropriate test/bench suite environment variables.
This setup is used so that executing a test or benchmark manually in the correct environment becomes as simple as possible:
Just `cd` into the directory and execute the run script.

The most important variable for run script authors is `TEST_DIR`,
which contains the absolute path to the test directory.
It can be used to source or run further scripts, e.g. `source "$TEST_DIR/util.sh` or `"$TEST_DIR/measure.py" ...`.

To distinguish being in a test or a benchmark, use the variable `TEST_BENCH`.
It is set (to `1`) when in the bench suite, and unset when in the test suite.
To check if you're in the bench suite, use `if [[ -n $TEST_BENCH ]]`.

It is recommended to source `"$TEST_DIR/util.sh"` immediately after sourcing the env file.
It configures sensible `set` options and defines a few useful helper functions.
See [`util.sh`](util.sh) for more details.

## Elab tests

The elab tests consist of the `tests/elab`, `tests/elab_fail`,and `tests/elab_bench` test piles.
They contain lean files that are elaborated by a `lean <file>` call.

- `elab`:
  Elaboration is expected to succeed with exit code 0.

- `elab_fail`:
  Elaboration is expected to fail with exit code 1.

- `elab_bench`:
  Like `elab`, but each lean file elaboration is also benchmarked.

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
  The test's stdout and stderr is captured in `<file>.out.produced`
  and then compared to `<file>.out.expected` (if present).
  The test fails if they differ.

- `<file>.exit.expected`:
  The test's exit code is captured in `<file>.exit.produced`
  and then compared to `<file>.exit.expected` (if present).
  The test fails if they differ.

These bash variables (set via `<file>.init.sh`) are used by the run script:

- `TEST_LEAN_ARGS`:
  A bash array of additional arguments to the `lean` command.

## Compile tests

The compile tests consist of the `tests/compile` and `tests/compile_bench` test piles.
They contain lean files with a `main` method.
The lean files are compiled, and any errors immediately cause the test to fail.
The resulting executable is then executed.
In the test suite, the lean files are also interpreted using `lean --run <file>`.

- `compile`:
  Files are only being tested.

- `compile_bench`:
  Files are both being tested and benchmarked.

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
  The test's stdout and stderr is captured in `<file>.out.produced`
  and then compared to `<file>.out.expected` (if present).
  The test fails if they differ.

- `<file>.exit.expected`:
  The test's exit code is captured in `<file>.exit.produced`
  and then compared to `<file>.exit.expected` (if present).
  The test fails if they differ.

These bash variables (set via `<file>.init.sh`) are used by the run script:

- `TEST_LEAN_ARGS`:
  A bash array of additional arguments to the `lean` command used to compile the lean file.

- `TEST_LEANC_ARGS`:
  A bash array of additional arguments to the `leanc` command used to compile the c file.

- `TEST_LEANI_ARGS`:
  A bash array of additional arguments to the `lean --run <file>` command used to interpret the lean file.

- `TEST_ARGS`:
  A bash array of arguments to the compiled (or interpreted) program.

