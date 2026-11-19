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
when fixing a specific file in the stage 2 build. But to invalidate any files that already passed the
stage 2 build (as well as for final validation),

```bash
make -C build/release/stage2 clean-stdlib
```

must be run manually before building.

To rebuild individual stage 2 modules without a full `make stage2`, use Lake directly:

```bash
cd build/release/stage2 && lake build Init.Prelude
```

To run tests in stage2, replace `-C build/release` with `-C build/release/stage2` in the usual test
commands (see the project `.claude/CLAUDE.md` "Running Tests" section).
