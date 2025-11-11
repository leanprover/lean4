When asked to implement new features:
* begin by reviewing existing relevant code and tests
* write comprehensive tests first (expecting that these will initially fail)
* and then iterate on the implementation until the tests pass.

To build Lean you should use `make -j$(nproc) -C build/release`.

To run a test you should use `cd tests/lean/run && ./test_single.sh example_test.lean`.

*Never* report success on a task unless you have verified both a clean build without errors, and that the relevant tests pass. You have to keep working until you have verified both of these.

All new tests should go in `tests/lean/run/`. Note that these tests don't have expected output, and just run on a success or failure basis. So you should use `#guard_msgs` to check for specific messages.

If you are not following best practices specific to this repository and the user expresses frustration, stop and ask them to help update this `.claude/CLAUDE.md` file with the missing guidance.