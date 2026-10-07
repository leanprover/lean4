---
name: stage2-build
description: Build and run tests against the stage2 Lean compiler. Use when asked to build, rebuild, or test against stage2.
allowed-tools: Bash, Read
---

# Testing Stage 2

Building stage2 is expensive, so confirm with the user before starting a stage2 build.

Build it as follows:

```bash
make -C build/release stage2 -j$(nproc)
```

Stage 2 is *not* automatically invalidated by changes to `src/`, which allows for faster iteration
when fixing a specific file in the stage 2 build.

**Trap: this means a plain `make stage2` after editing `src/` does NOT reflect your change.** The
already-built stage2 stdlib and `bin/lean` keep using the *old* code (Lake traces the toolchain by
git commit hash, which local edits don't change), so any tests run afterward silently exercise the
old behavior — their pass/fail is meaningless. This bites hardest for **compiler changes**
(`src/Lean/**`, codegen/elaboration/IR), which affect how the *whole* stdlib is built.

So before running tests to validate any change — and always for final validation — invalidate first:

```bash
make -C build/release/stage2 clean-stdlib
```

then build. Only skip `clean-stdlib` while iterating on a single file whose output you inspect
directly; never when trusting test results.

To rebuild individual stage 2 modules without a full `make stage2`, use Lake directly:

```bash
cd build/release/stage2 && lake build Init.Prelude
```

To run tests in stage2, replace `-C build/release` with `-C build/release/stage2` in the usual test
commands (see the project `.claude/CLAUDE.md` "Running Tests" section).
