# Building `lean.js` with Emscripten

Lean can be cross-compiled to WebAssembly with [Emscripten](https://emscripten.org/). The result is a command-line `lean` for Node.js: `bin/lean.js` and `bin/lean.wasm`, started through the `bin/lean` launcher script. Lake, `leanc` and the other tools are not built for this target, and the build is not released. The "Web Assembly" job in [`.github/workflows/ci.yml`](../../.github/workflows/ci.yml) builds and tests it on nightlies, on releases and on PRs labeled `release-ci`; its `CMAKE_OPTIONS` there and the Emscripten SDK version in [`.github/workflows/build-template.yml`](../../.github/workflows/build-template.yml) are the authoritative configuration. This page explains how that build is put together.

## Requirements

- The [Emscripten SDK](https://github.com/emscripten-core/emsdk) at the version `build-template.yml` installs, installed and activated.
- Node.js on the `PATH` to run `lean.js`; the CI job installs Node.js 26. `emcc` itself uses the Node.js bundled with the SDK.
- A native toolchain and 32-bit libraries for stage 0; on Ubuntu `clang`, `gcc-multilib`, `g++-multilib`, `libuv1-dev:i386`, `libssl-dev:i386` and `pkgconf:i386`, in addition to the [usual build tools](index.md).

## How the build works

As in a native build, stage 0 compiles stage 1 (see [bootstrapping](../dev/bootstrap.md)), but the two stages target different platforms:

1. Stage 0 is a native 32-bit `lean`, built with `clang -m32` against the i386 libraries, without GMP and without `mmap` (the `STAGE0_*` options). It compiles the `.olean` files of stage 1, which must come from a 32-bit compiler because `lean.wasm` is a 32-bit program and `.olean` files depend on the pointer size.
2. Stage 1 is cross-compiled with Emscripten's CMake toolchain file and archived with `emar`. It builds libuv itself, uses neither GMP, `mmap` nor mimalloc, and links `Init`, `Std`, `Lean`, the runtime and the shell statically into `lean.js` and `lean.wasm`. The interpreter finds compiled Lean code by symbol name; natively the dynamic symbol table answers that (`-rdynamic`), in `lean.js` a table inside the module does: `script/wasm_symbols.py` reads the symbols of the Lean archives from their object files and writes `lib/temp/lean_symbols.c`, which `stdlib.make` compiles and links into `lean.js`, and `lib/temp/lean_exports.json`, the symbols of the runtime archives that `lean.wasm` exports for `dlsym` (`-sMAIN_MODULE=2 -sEXPORTED_FUNCTIONS`). The Emscripten flags are set in `src/CMakeLists.txt`.

Under Node.js, `lean.js` mounts the host's `/home` and `/tmp` into Emscripten's virtual file system and changes into the host's working directory there (`lean_main` in `src/util/shell.cpp`), so it can only read and write files below these two directories and must be started from a directory below one of them.

## Building

Take the "Web Assembly" entry's `CMAKE_OPTIONS` from `ci.yml`, replace `$GITHUB_WORKSPACE/emsdk/emsdk-main` with your emsdk directory, and run in a fresh `build` directory, with the emsdk activated and Node.js on the `PATH`:

```bash
cmake .. --preset release -B . <CMAKE_OPTIONS> -DLEAN_INSTALL_PREFIX=$PWD/..
make stage1 -j$(nproc)
make -C stage1 install
```

The last command installs into `lean-<version>-linux_wasm32`. Linking `lean.js` is the expensive part: one link of the C++ runtime's LTO bitcode together with the Lean-generated code, followed by emcc's JavaScript passes.

## Running tests

`stage1/bin/lean` runs `node --stack-size=8192 lean.js` with its arguments, so the test suite can call `lean` as usual. A `lean.js` process spends about 10 s of CPU initializing Lean (V8 compiles the module lazily, so the time is Lean's own) and needs between one and three gigabytes of memory, so the whole `elab` pile would take hours. CI runs 177 tests in parallel. They are listed as `wasmTests` in the matrix script of `ci.yml`, next to the two `grep` patterns that select them: the `elab` and `elab_fail` tests that execute code whose behaviour depends on the platform (word size, floating point, byte arrays, bignums, the file system, tasks, hashing, platform APIs), without those that cannot work in `lean.js`, plus the `misc` scripts that test the command line and `markdown_conformance`. Tests that spawn processes (`bv_decide` runs CaDiCaL), import Lake or LeanExport, rely on environment variables from their `.init.sh`, on Linux-only behaviour or on a 64-bit word size cannot work in `lean.js`; `importModules` of `Lean` on top of `import Lean` exhausts the 2 GB wasm32 heap, and deep recursion overflows the 4 MB stack of a Node.js worker thread with a JavaScript `RangeError`. The other piles need `leanc`, Lake, the libuv bindings that the wasm build stubs out, or a `lean --server` child process.

To run the job's tests locally, take the `ctest` command from the Test step of a `Web Assembly` job log and run it from the repository root, or pass your own `-R` to `ctest --preset release --test-dir build/stage1`. `lean` starts one Node.js worker thread per task-manager thread, so pass `-j4` (or the test suite's `TEST_LEAN_ARGS=-j4`) on machines with many cores. Two rare failures come from `lean.js` itself and are retried by the job: a hang under load, and a trap at exit after the complete output of a `lean --run` process.
