# Building `lean.js` with Emscripten

Lean can be cross-compiled to WebAssembly with [Emscripten](https://emscripten.org/). The result is a command-line `lean` for Node.js: `bin/lean.js` and `bin/lean.wasm`, started through the `bin/lean` launcher script. Lake, `leanc` and the other tools are not built for this target, and the build is not released. The "Web Assembly" job in [`.github/workflows/ci.yml`](../../.github/workflows/ci.yml) builds and tests it on nightlies, on releases and on PRs labeled `release-ci`; its `CMAKE_OPTIONS` there and the Emscripten SDK version in [`.github/workflows/build-template.yml`](../../.github/workflows/build-template.yml) are the authoritative configuration. This page explains how that build is put together.

## Requirements

- The [Emscripten SDK](https://github.com/emscripten-core/emsdk) at the version `build-template.yml` installs, installed and activated.
- Node.js 24 or newer on the `PATH` to run `lean.js`: `lean.wasm` exports all of its about 250,000 symbols, and V8 accepts more than 100,000 exports only from Node.js 24 on. `emcc` itself uses the Node.js bundled with the SDK.
- A native toolchain and 32-bit libraries for stage 0; on Ubuntu `clang`, `gcc-multilib`, `g++-multilib`, `libuv1-dev:i386`, `libssl-dev:i386` and `pkgconf:i386`, in addition to the [usual build tools](index.md).

## How the build works

As in a native build, stage 0 compiles stage 1 (see [bootstrapping](../dev/bootstrap.md)), but the two stages target different platforms:

1. Stage 0 is a native 32-bit `lean`, built with `clang -m32` against the i386 libraries, without GMP and without `mmap` (the `STAGE0_*` options). It compiles the `.olean` files of stage 1, which must come from a 32-bit compiler because `lean.wasm` is a 32-bit program and `.olean` files depend on the pointer size.
2. Stage 1 is cross-compiled with Emscripten's CMake toolchain file and archived with `emar`. It builds libuv itself, uses neither GMP, `mmap` nor mimalloc, and links `Init`, `Std`, `Lean`, the runtime and the shell statically into `lean.js` and `lean.wasm`. The link uses `-sMAIN_MODULE=1 -sEXPORT_ALL=1` so that every symbol stays available to the interpreter, as `-rdynamic` does natively; the Emscripten flags are set in `src/CMakeLists.txt`.

Under Node.js, `lean.js` mounts the host's `/home` and `/tmp` into Emscripten's virtual file system and changes into the host's working directory there (`lean_main` in `src/util/shell.cpp`), so it can only read and write files below these two directories and must be started from a directory below one of them.

## Building

Take the "Web Assembly" entry's `CMAKE_OPTIONS` from `ci.yml`, replace `$GITHUB_WORKSPACE/emsdk/emsdk-main` with your emsdk directory, and run in a fresh `build` directory, with the emsdk activated and Node.js 24 or newer on the `PATH`:

```bash
cmake .. --preset release -B . <CMAKE_OPTIONS> -DLEAN_INSTALL_PREFIX=$PWD/..
make stage1 -j$(nproc)
make -C stage1 install
```

The last command installs into `lean-<version>-linux_wasm32`. Linking `lean.js` is the expensive part: one link of the C++ runtime's LTO bitcode together with the Lean-generated code, followed by emcc's JavaScript passes over a file of more than 100 MiB, for which `src/stdlib.make.in` raises Node.js's heap limit.

## Running tests

`stage1/bin/lean` runs `node --stack-size=8192 lean.js` with its arguments, so the test suite can call `lean` as usual. A WebAssembly `lean` process can need several gigabytes of memory and is slow, so CI runs only a few tests, one at a time. From the repository root:

```bash
ctest --preset release --test-dir build/stage1 --no-tests=error -j1 -R '^(elab_fail/1007|elab/(Format|1037|ac_rfl|tempfile|libuv))\.lean$'
```
