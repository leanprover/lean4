# Lean 4 DevContainer

This configuration provides a development environment for Lean 4 in GitHub Codespaces or VS Code Remote Containers.

## Quick Start

1. Open in GitHub Codespaces or VS Code with Remote Containers extension
2. Wait for container build (one-time setup)
3. Start developing - toolchains are pre-configured

## Common Commands

```bash
# Build Lean 4
make -C build/release -j$(nproc)

# Run tests
make -C build/release test

# Run specific test
cd tests/lean && ./test_single.sh test_file.lean
```

## Key Features

- Automatic toolchain switching based on directory (`lean4-stage0` in src/, `lean4` in tests/)
- Pre-configured build tasks (Ctrl+Shift+B)
- Debugging support with gdb and rr
- Persistent ccache for faster rebuilds

## Documentation

- [Development Guide](../doc/dev/index.md)
- [Building Lean](../doc/make/index.md)
- [Testing](../doc/dev/testing.md)
- [Debugging](../doc/dev/debugging.md)