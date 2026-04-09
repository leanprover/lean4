# Test suite

This directory contains the lean test and benchmark suite.

The test suite consists of two types of directories: Test directories and test piles.

A **test directory** is a directory containing a `run_test.sh` and/or a `run_bench.sh` script.
It represents a single test or benchmark, depending on which script is present.
The run scripts are executed once with their working directory set to the test directory.

A **test pile** is also a directory containing a `run_test.sh` and/or a `run_bench.sh` script.
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
  These are also executed as part of the test suite, and `.out.expected` files are ignored when benchmarking.
- `docparse`:
  Docstring parsing tests.
- `elab`:
  Tests that elaborate lean files without executing them, verifying the resulting output.
- `elab_fail`:
  Like `elab`, but expecting an exit code of 1 instead of 0.
- `elab_bench`:
  Like `elab`, but measuring the elaboration performance.
  These are also executed as part of the test suite, and `.out.expected` files are ignored when benchmarking.
- `server`, `server_interactive`:
  Test LSP server requests.
- `lake:`
  Test suite for lake.
  It is mostly isolated from the rest of the test suite and follows its own conventions.
- `lake_bench`:
  Benchmark directories that measure lake performance.
- `misc`:
  A collection of miscellaneous small test scripts.
- `misc_bench`:
  A collection of miscellaneous small benchmark scripts.
- `pkg`:
  Tests that run in lake packages.

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

Run an individual test using one of these commands.
Note that regex arguments to `-R` need to be double-quoted
if they contain any special shell characters like `|`.

```sh
CTEST_PARALLEL_LEVEL="$(nproc)" CTEST_OUTPUT_ON_FAILURE=1 \
make -C build/release -j "$(nproc)" test ARGS="-R '<regex>'"

# For a specific stage
CTEST_PARALLEL_LEVEL="$(nproc)" CTEST_OUTPUT_ON_FAILURE=1 \
make -C build/release/stage1 -j "$(nproc)" test ARGS="-R '<regex>'"

# Manually, without ctest
tests/with_stage1_test_env.sh path/to/test/directory/run_test.sh
tests/with_stage1_test_env.sh path/to/test/pile/run_test.sh testfile
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

Run an individual benchmark manually using one of these commands.
Note that the `run_bench.sh` arguments are relative to the test directory, not the current working directory.

```sh
tests/with_stage1_bench_env.sh path/to/test/directory/run_bench.sh
tests/with_stage1_bench_env.sh path/to/test/pile/run_bench.sh testfile
```

## How to write a test?

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
2. Write a `run_test.sh` and/or `run_bench.sh` script.
3. Add the directory to the [`CMakeLists.txt`](CMakeLists.txt) file,
   next to the other tests near the bottom.
4. Document the new directory in this readme file
   by updating the directory structure section above.
5. Optionally update [`lint.py`](lint.py) if it makes sense.

## How to write a benchmark?

When writing a benchmark, consider that most benchmarks are also executed as tests.
You can check that this is the case if a `run_test.sh` script exists next to the `run_bench.sh` script in the directory.
When run as benchmark, the problem instance should be large enough to result in reliable measurements.
When run as test, the problem instance should be as small as possible, but large enough to still test the different code paths.

The main mechanism to scale problem instances is the `TEST_BENCH` environment variable.
It is unset in tests and set to `1` in benchmarks.
Inside your benchmark, check whether the variable exists and adjust the problem size accordingly:

```lean
let bench := (← IO.getEnv "TEST_BENCH") == some "1"
```

Inside the `compile_bench` directory, there is a second mechanism:
Using a `.init.sh` file to pass command line arguments to your test.
This is useful if you also want to generate graphs for your parametric benchmarks.
See [`tests/compile_bench/binarytrees.lean`](tests/compile_bench/binarytrees.lean) as an example.

If you want custom metrics aside from the usual `instructions`, `wall-clock`, ...
inside the `elab_bench` or `compile_bench` directories,
you can print them to stdout in the format `measurement: <name> <value>[ <unit>]`,
e.g. `measurement: size 1337 B` or `measurement: iterations 42`.
See [`tests/compile_bench/ilean_roundtrip.lean`](tests/compile_bench/ilean_roundtrip.lean) as an example.

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

Test and bench scripts must be named `run_test.sh` and `run_bench.sh` respectively.
They are sourced by the `with_*_env.sh` script,
which provides a set of environment variables and definitions.
Because of this, they require no shebang and should not be executable.

The most notable environment variables are:

- `TEST_DIR`: Absolute path to the `tests` directory.
- `SCRIPT_DIR`: Absolute path to the `script` directory.
- `TEST_BENCH`: Set to `1` if we're currently executing a benchmark, unset otherwise.

The definitions come from `util.sh`,
which provides a few utility functions and also uses `set` to set sensible bash defaults.

The run scripts are always executed with their working directory set to their surrounding directory.
Inside a test pile, `run_test.sh` and `run_bench.sh` receive
a relative path to the file under test as their first (and only) argument.
Inside a test directory, they receive no arguments.

A test succeeds iff the `run_test.sh` script exits with exit code 0.
A benchmark additionally must produce a measurements file:
Inside a test pile, `run_bench.sh` is expected to produce a `<testfile>.measurements.jsonl` file.
Inside a test directory, `run_bench.sh` is expected to produce a `measurements.jsonl` file.

## The `elab*` test pile

These files are available to configure a test:

- `<file>.init.sh`:
  This file is sourced at the start of the run script.
  Configure the run script by setting bash variables here.

- `<file>.before.sh`:
  This file is executed before the test/benchmark.
  Delete temporary resources created by previous test runs here if necessary.
  Don't create temporary resources here, the test file should do so itself if possible.
  That way, they're also available when opening the file in your editor.

- `<file>.after.sh`:
  This file is executed after the test/benchmark.
  Don't delete temporary resources here; do so in `<file>.before.sh` if necessary.
  Instead, add any temporary resources to the directory's `.gitignore` file.

- `<file>.out.expected`:
  The test fails if its stdout and stderr doesn't match this file's contents.
  If this file isn't present, the test's output must be empty.

- `<file>.out.ignored`:
  Ignore the test's output entirely; don't compare it to `<file>.out.expected`.

These bash variables (set via `<file>.init.sh`) are used by the run script:

- `TEST_LEAN_ARGS`:
  A bash array of additional arguments to the `lean` command.

- `TEST_EXIT`:
  A bash variable containing the expected exit code of the program.
  When set to `nonzero` instead of a numerical value, the exit code must not be 0.

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
  Delete temporary resources created by previous test runs here if necessary.
  Don't create temporary resources here, the test file should do so itself if possible.
  That way, they're also available when opening the file in your editor.

- `<file>.after.sh`:
  This file is executed after the test/benchmark.
  Don't delete temporary resources here; do so in `<file>.before.sh` if necessary.
  Instead, add any temporary resources to the directory's `.gitignore` file.

- `<file>.out.expected`:
  The test fails if its stdout and stderr doesn't match this file's contents.
  If this file isn't present, the test's output must be empty.

- `<file>.out.ignored`:
  Ignore the test's output entirely; don't compare it to `<file>.out.expected`.

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

- `TEST_EXIT`:
  A bash variable containing the expected exit code of the program.
  When set to `nonzero` instead of a numerical value, the exit code must not be 0.

## The `interactive` test pile

These tests are designed to test LSP server requests at a given position in the input file.
Each `.lean` file contains comments that indicate how to simulate a client request at a position,
using a `--^` point to the line position.

Example:

```lean,ignore
open Foo in
theorem tst2 (h : a ≤ b) : a + 2 ≤ b + 2 :=
Bla.
  --^ completion
```

In this example, the test driver will simulate an auto-completion request at `Bla.`.
The expected output is stored in the corresponding `.out.expected` file
in the json format that is part of the
[Language Server Protocol](https://microsoft.github.io/language-server-protocol/).

This can also be used to test the following additional requests:

```
--^ textDocument/hover
--^ textDocument/typeDefinition
--^ textDocument/definition
--^ $/lean/plainGoal
--^ $/lean/plainTermGoal
--^ insert: ...
--^ collectDiagnostics
```
