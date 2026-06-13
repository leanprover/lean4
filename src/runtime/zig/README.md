# Zig Runtime Shadow

This directory contains the Zig reimplementation of the Lean 4 runtime.
It is a work-in-progress shadow tree intended to eventually replace the C++
runtime under `src/runtime/` for selected targets.

## Layout

- `*.zig`: Zig reimplementation of runtime subsystems.
- `box_weak_exports.c`, `io_error_weak_exports.c`: C weak exports used during
  split-runtime linking.
- `testabi_hidden_shims.c`: malloc-backed shims for ABI smoke tests that do not
  link mimalloc.

## Build

There is no top-level CMake integration yet. The previous standalone
`zig-backend/` build is being migrated; for now use the Zig CLI directly:

```bash
cd src/runtime/zig
zig build --build-file ../../../zig-backend/build.zig  # TODO: migrate build.zig
```

## Status

M1-M6 functionality has been ported from `zig-backend/`. Full in-tree build
integration is pending.
