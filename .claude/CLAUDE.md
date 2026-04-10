(In the following, use `sysctl -n hw.logicalcpu` instead of `nproc` on macOS)

## Building

To build Lean you should use `make -j$(nproc) -C build/release`.

The build uses `ccache`, and in a sandbox `ccache` may complain about read-only file systems.
Use `CCACHE_READONLY` and `CCACHE_TEMPDIR` instead of disabling ccache completely.

To rebuild individual modules without a full build, use Lake directly:
```
cd src && lake build Init.Prelude
```

## Running Tests

See `tests/README.md` for full documentation. Quick reference:

```bash
# Full test suite (use after builds to verify correctness)
CTEST_PARALLEL_LEVEL="$(nproc)" CTEST_OUTPUT_ON_FAILURE=1 \
make -C build/release -j "$(nproc)" test

# Specific test by name (supports regex via ctest -R; double-quote special chars like |)
CTEST_PARALLEL_LEVEL="$(nproc)" CTEST_OUTPUT_ON_FAILURE=1 \
make -C build/release -j "$(nproc)" test ARGS="-R 'grind_ematch'"

# Multiple tests matching a pattern
CTEST_PARALLEL_LEVEL="$(nproc)" CTEST_OUTPUT_ON_FAILURE=1 \
make -C build/release -j "$(nproc)" test ARGS="-R 'treemap|phashmap'"

# Rerun only previously failed tests
CTEST_PARALLEL_LEVEL="$(nproc)" CTEST_OUTPUT_ON_FAILURE=1 \
make -C build/release -j "$(nproc)" test ARGS='--rerun-failed'

# Run a test manually without ctest (test pile: pass filename relative to the pile dir)
tests/with_stage1_test_env.sh tests/elab_bench/run_bench.sh cbv_decide.lean
tests/with_stage1_test_env.sh tests/elab/run_test.sh grind_indexmap.lean
```

## Benchmark vs Test Problem Sizes

Benchmarks are also run as tests. Use the `TEST_BENCH` environment variable (unset in tests, set to `1` in benchmarks) to scale problem sizes:

- In `compile_bench` `.init.sh` files: check `$TEST_BENCH` and set `TEST_ARGS` accordingly
- In `elab_bench` Lean files: use `(← IO.getEnv "TEST_BENCH") == some "1"` to switch between small (test) and large (bench) inputs

See `tests/README.md` for the full benchmark writing guide.

## Testing stage 2

When requested to test stage 2, build it as follows:
```
make -C build/release stage2 -j$(nproc)
```
Stage 2 is *not* automatically invalidated by changes to `src/` which allows for faster iteration
when fixing a specific file in the stage 2 build but for invalidating any files that already passed
the stage 2 build as well as for final validation,
```
make -C build/release/stage2 clean-stdlib
```
must be run manually before building.

To rebuild individual stage 2 modules without a full `make stage2`, use Lake directly:
```
cd build/release/stage2 && lake build Init.Prelude
```

To run tests in stage2, replace `-C build/release` from above with `-C build/release/stage2`.

## New features

When asked to implement new features:
* begin by reviewing existing relevant code and tests
* write comprehensive tests first (expecting that these will initially fail)
* and then iterate on the implementation until the tests pass.

## Success Criteria

*Never* report success on a task unless you have verified both a clean build without errors, and that the relevant tests pass.

## Build System Safety

**NEVER manually delete build directories** (build/, stage0/, stage1/, etc.) even when builds fail.
- ONLY use the project's documented build command: `make -j$(nproc) -C build/release`
- If a build is broken, ask the user before attempting any manual cleanup

## stage0 Is a Copy of src

**Never manually edit files under `stage0/`.** The `stage0/` directory is a snapshot of `src/` produced by `make update-stage0`. To change anything in stage0 (CMakeLists.txt, C++ source, etc.), edit the corresponding file in `src/` and let `update-stage0` propagate it.

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
