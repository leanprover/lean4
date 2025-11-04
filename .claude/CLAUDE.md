To build Lean you should use `make -j$(nproc) -C build/release`.

To run a test you should use `cd tests/lean/run && ./test_single.sh example_test.lean`.

## New features

When asked to implement new features:
* begin by reviewing existing relevant code and tests
* write comprehensive tests first (expecting that these will initially fail)
* and then iterate on the implementation until the tests pass.

All new tests should go in `tests/lean/run/`. These tests don't have expected output; we just check there are no errors. You should use `#guard_msgs` to check for specific messages.

## Success Criteria

*Never* report success on a task unless you have verified both a clean build without errors, and that the relevant tests pass.

## LSP and IDE Diagnostics

After rebuilding, LSP diagnostics may be stale until the user interacts with files. Trust command-line test results over IDE diagnostics.

## Update prompting when the user is frustrated

If the user expresses frustration with you, stop and ask them to help update this `.claude/CLAUDE.md` file with missing guidance.
