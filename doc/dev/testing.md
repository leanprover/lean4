# Unit Testing

You can run the unit tests after completing a build using the following:

After [building lean](../make/index.md) you can run all the tests using
```
cd build/release
make test ARGS=-j4
```

Change the 4 to the maximum number of parallel tests you want to
allow. The best choice is the number of CPU cores on your machine as
the tests are mostly CPU bound.  You can find the number of processors
on linux using `nproc` and on Windows it is the `NUMBER_OF_PROCESSORS`
environment variable.

You can run tests after [building a specific stage](bootstrap.md) by
adding the `-C stageN` argument. The default when run as above is stage 1.  The
Lean tests will automatically use that stage's corresponding Lean
executables

You can also use `ctest` directly if you are in the right folder.  So
to run stage1 tests with a 300 second timeout run this:

```bash
cd build/release/stage1
ctest -j 4 --output-on-failure --timeout 300
```

To get verbose output from ctest pass the `--verbose` command line
option. Test output is normally suppressed and only summary
information is displayed. This option will show all test output

Here is the summary of the test source code organization.
All these tests are included by [/src/shell/CMakeLists.txt](https://github.com/leanprover/lean4/blob/master/src/shell/CMakeLists.txt):

- `tests/lean`: contains tests that come equipped with a
  .lean.expected.out file. The driver script `test_single.sh` runs
  each test and checks the actual output (*.produced.out) with the
  checked in expected output.

- `tests/lean/run`: contains tests that are run through the lean
  command line one file at a time. These tests only look for error
  codes and do not check the expected output even though output is
  produced, it is ignored.

- `tests/lean/interactive`: are designed to test server requests at a
  given position in the input file. Each .lean file contains comments
  that indicate how to simulate a client request at that position.
  using a `--^` point to the line position. Example:
    ```lean,ignore
    open Foo in
    theorem tst2 (h : a ≤ b) : a + 2 ≤ b + 2 :=
    Bla.
      --^ textDocument/completion
    ```
    In this example, the test driver `test_single.sh` will simulate an
    auto-completion request at `Bla.`. The expected output is stored in
    a .lean.expected.out in the json format that is part of the
    [Language Server
    Protocol](https://microsoft.github.io/language-server-protocol/).

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

- `tests/lean/server`: Tests more of the Lean `--server` protocol.
  There are just a few of them, and it uses .log files containing
  JSON.

- `tests/compiler`: contains tests that will run the Lean compiler and
  build an executable that is executed and the output is compared to
  the .lean.expected.out file. This test also contains a subfolder
  `foreign` which shows how to extend Lean using C++.

- `tests/lean/trust0`: tests that run Lean in a mode that Lean doesn't
  even trust the .olean files (i.e., trust 0).

- `tests/bench`: contains performance tests.

- `tests/plugin`: tests that compiled Lean code can be loaded into
  `lean` via the `--plugin` command line option.

- `tests/leanpkg`: tests the `leanpkg` program, where each sub-folder
  is a complete "lean package", including:
    - `cyclic`
    - `user_ext`
    - `user_attr`
    - `user_opt`
    - `prv`
    - `user_attr_app`
