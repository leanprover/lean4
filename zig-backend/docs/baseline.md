# Lean 4 Baseline Build Documentation

This document records the baseline Lean 4 stage1 build produced for the
Zig-backend mission (M1-F2-baseline-lean).

## Build Environment

- **Host**: macOS 25.4.0 (arm64-apple-darwin)
- **Logical CPUs**: 12
- **Compiler**: Apple clang 17.0.0
- **CMake**: 4.3.0
- **Make**: GNU Make 3.81
- **ccache**: 4.13.6 (installed via Homebrew)
- **Free disk before build**: 41.4 GB
- **Free disk after build**: 36.8 GB

## Build Invocation

```bash
cd /Users/davirian/dev/active/lean4
cmake --preset release
make -j$(sysctl -n hw.logicalcpu) -C build/release
```

## Lean Binary

- **Path**: `/Users/davirian/dev/active/lean4/build/release/stage1/bin/lean`
- **Size**: 33456 bytes
- **Permissions**: `-rwxr-xr-x`

## Version Output

```
Lean (version 4.31.0-pre, arm64-apple-darwin25.4.0, commit e09155b6f91642c2e50c3eb476823947200a90d0, Release)
```

## Verification

- `lean --version` exits with code `0`.
- Version string matches `4\.[0-9]+\.[0-9]+`.

## Notes

- The build completed successfully (4815 jobs).
- `build/release/` now contains stage0, stage1, and all intermediate artifacts.
- This baseline is used by subsequent M1 and M2 features (e.g., M2-F12 lean-smoke test).
