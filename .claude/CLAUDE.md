To build Lean you should use `make -j -C build/release`.

## Running Tests

See `doc/dev/testing.md` for full documentation. Quick reference:

```bash
# Full test suite (use after builds to verify correctness)
make -j -C build/release test ARGS="-j$(nproc)"

# Specific test by name (supports regex via ctest -R)
make -j -C build/release test ARGS='-R grind_ematch --output-on-failure'

# Rerun only previously failed tests
make -j -C build/release test ARGS='--rerun-failed --output-on-failure'

# Single test from tests/lean/run/ (quick check during development)
cd tests/lean/run && ./test_single.sh example_test.lean

# ctest directly (from stage1 build dir)
cd build/release/stage1 && ctest -j$(nproc) --output-on-failure --timeout 300
```

The full test suite includes `tests/lean/`, `tests/lean/run/`, `tests/lean/interactive/`,
`tests/compiler/`, `tests/pkg/`, Lake tests, and more. Using `make test` or `ctest` runs
all of them; `test_single.sh` in `tests/lean/run/` only covers that one directory.

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

**Body format:** The first paragraph must start with "This PR". This paragraph is automatically incorporated into release notes. Use imperative present tense. Include motivation and contrast with previous behavior when relevant. Do NOT use markdown headings (`## Summary`, `## Test plan`, etc.) in PR bodies.

Example:
```
feat: add optional binder limit to `mkPatternFromTheorem`

This PR adds a `num?` parameter to `mkPatternFromTheorem` to control how many
leading quantifiers are stripped when creating a pattern.
```

**Changelog labels:** Add one `changelog-*` label to categorize the PR for release notes:
- `changelog-language` - Language features and metaprograms
- `changelog-tactics` - User facing tactics
- `changelog-server` - Language server, widgets, and IDE extensions
- `changelog-pp` - Pretty printing
- `changelog-library` - Library
- `changelog-compiler` - Compiler, runtime, and FFI
- `changelog-lake` - Lake
- `changelog-doc` - Documentation
- `changelog-ffi` - FFI changes
- `changelog-other` - Other changes
- `changelog-no` - Do not include this PR in the release changelog

If you're unsure which label applies, it's fine to omit the label and let reviewers add it.

## Module System for `src/` Files

Files in `src/Lean/`, `src/Std/`, and `src/lake/Lake/` must have both `module` and `prelude` (CI enforces `^prelude$` on its own line). With `prelude`, nothing is auto-imported — you must explicitly import `Init.*` modules for standard library features. Check existing files in the same directory for the pattern, e.g.:

```lean
module

prelude
import Init.While  -- needed for while/repeat
import Init.Data.String.TakeDrop  -- needed for String.startsWith
public import Lean.Compiler.NameMangling  -- public if types are used in public signatures
```

Files outside these directories (e.g. `tests/`, `script/`) use just `module`.

## CI Log Retrieval

When CI jobs fail, investigate immediately - don't wait for other jobs to complete. Individual job logs are often available even while other jobs are still running. Try `gh run view <run-id> --log` or `gh run view <run-id> --log-failed`, or use `gh run view <run-id> --job=<job-id>` to target the specific failed job. Sleeping is fine when asked to monitor CI and no failures exist yet, but once any job fails, investigate that failure immediately.

## Copyright Headers

New files require a copyright header. To get the year right, always run `date +%Y` rather than relying on memory. The copyright holder should be the author or their current employer — check other recent files by the same author in the repository to determine the correct entity (e.g., "Lean FRO, LLC", "Amazon.com, Inc. or its affiliates").

Test files (in `tests/`) do not need copyright headers.
