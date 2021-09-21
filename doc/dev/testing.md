# Unit Testing

You can run the unit tests after completing a build using the following:

```bash
cd build/release/stage0
ctest -j 4 --output-on-failure --timeout 300
```

You can increase the parallelism from 4 to as many cores you have
available to decrease overall test time.  You can also increase the timeout
from 300 seconds if you need to.

Here is the summary of the test source code organization.
All these tests are included by [~/src/shell/CMakeLists.txt](https://github.com/leanprover/lean4/blob/master/src/shell/CMakeLists.txt):

- `tests/lean`: contains tests that come equipped with a
  .lean.expected.out file. The driver script `test_single.sh` runs
  each test and checks the actual output (*.produced.out) with the
  checked in expected output.

- `tests/lean/run`: contains tests that are run through the lean
  command line one file at a time. These tests only look for error
  codes and do not check the expected output even though output is
  produced, it is ignored.

- `tests/lean/interactive`: are designed to test auto-completion
  requests at a given position in the input file. Each .lean files
  contain comments that indicate how to simulate a client request at
  that position. using a `--^` point to the line position. Example:
    ```lean
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

- `tests/lean/server`: Tests more of the lean `--server` protocol.
  There are just a few of them, and it uses .log files containing
  JSON.

- `tests/compiler`: contains tests that will run the lean compiler and
  build an executable that is executed and the output is compared to
  the .lean.expected.out file. This test also contains a subfolder
  `foreign` which shows how to extend Lean using C++.

- `tests/lean/trust0`: tests that run Lean in a mode that Lean doesn't
  even trust the .olean files (i.e., trust 0).

- `tests/bench`: contains performance tests.

- `tests/plugin`: tests that one compiled lean program can call
  another compiled lean program via the `--plugin` command line
  option.

- `tests/leanpkg`: tests the `leanpkg` program, where each sub-folder
  is a complete "lean package", including:
    - `cyclic`
    - `user_ext`
    - `user_attr`
    - `user_opt`
    - `prv`
    - `user_attr_app`
