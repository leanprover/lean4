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

The Zig runtime is opt-in and experimental. Default Lean builds continue to use
the C++ runtime and do not require Zig.

Build the runtime archive manually from an existing stage1 build:

```bash
make -C build/release/stage1 leanrt_zig
```

Configure the full release build with the Zig runtime path enabled:

```bash
cmake --preset release -B build/release -DLEAN_ZIG_RUNTIME=ON
make -j$(sysctl -n hw.logicalcpu) -C build/release
```

Run the opt-in runtime tests:

```bash
ctest --preset release --test-dir build/release/stage1 -R 'runtime/zig|emitzig/zigrt|emitzig/zig-symbols'
```

## Status

M1-M6 functionality has been ported from `zig-backend/`. The in-tree CMake and
CTest path builds `libleanrt_zig.a`, runs Zig runtime unit tests, and runs one
EmitZig-to-Zig-runtime smoke test when `LEAN_ZIG_RUNTIME=ON`.
