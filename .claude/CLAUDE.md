To build Lean you should use `make -j -C build/release`.

To run a test you should use `cd tests/lean/run && ./test_single.sh example_test.lean`.

## New features

When asked to implement new features:
* begin by reviewing existing relevant code and tests
* write comprehensive tests first (expecting that these will initially fail)
* and then iterate on the implementation until the tests pass.

All new tests should go in `tests/lean/run/`. These tests don't have expected output; we just check there are no errors. You should use `#guard_msgs` to check for specific messages.

## Success Criteria

*Never* report success on a task unless you have verified both a clean build without errors, and that the relevant tests pass.

## Build System Safety

**NEVER manually delete build directories** (build/, stage0/, stage1/, etc.) even when builds fail.
- ONLY use the project's documented build command: `make -j -C build/release`
- If a build is broken, ask the user before attempting any manual cleanup

## LSP and IDE Diagnostics

After rebuilding, LSP diagnostics may be stale until the user interacts with files. Trust command-line test results over IDE diagnostics.

## Update prompting when the user is frustrated

If the user expresses frustration with you, stop and ask them to help update this `.claude/CLAUDE.md` file with missing guidance.

## Creating pull requests

Follow the commit convention in `doc/dev/commit_convention.md`.

**Title format:** `<type>: <subject>` where type is one of: `feat`, `fix`, `doc`, `style`, `refactor`, `test`, `chore`, `perf`.
Subject should use imperative present tense ("add" not "added"), no capitalization, no trailing period.

**Body format:** The first paragraph must start with "This PR". This paragraph is automatically incorporated into release notes. Use imperative present tense. Include motivation and contrast with previous behavior when relevant.

Example:
```
feat: add optional binder limit to `mkPatternFromTheorem`

This PR adds a `num?` parameter to `mkPatternFromTheorem` to control how many
leading quantifiers are stripped when creating a pattern.
```

## CI Log Retrieval

When CI jobs fail, investigate immediately - don't wait for other jobs to complete. Individual job logs are often available even while other jobs are still running. Try `gh run view <run-id> --log` or `gh run view <run-id> --log-failed`, or use `gh run view <run-id> --job=<job-id>` to target the specific failed job. Sleeping is fine when asked to monitor CI and no failures exist yet, but once any job fails, investigate that failure immediately.
