# WebAssembly browser demos

Two demos side by side:

| Page | Module | Runtime |
|---|---|---|
| [index.html](./index.html) | pure scalars | none |
| [core_rt.html](./core_rt.html) | multi-module + constructors/RC | language-core `libleanrt` |

## Prerequisites

* Built Lean (`build/release/stage1/bin/lean` + `leanc`)
* `wasm-ld` / `wasm-validate` (WABT)
* For core runtime: `WASI_SDK_PATH` pointing at [wasi-sdk](https://github.com/WebAssembly/wasi-sdk/releases)

## Build

```bash
# Scalar-only (no WASI)
./build.sh

# Core runtime multi-module program
export WASI_SDK_PATH=/path/to/wasi-sdk
./build_core_rt.sh
```

## Run

```bash
python3 -m http.server 8765
```

* <http://localhost:8765/> — scalar demo
* <http://localhost:8765/core_rt.html> — core runtime demo

## What this is (and is not)

**Is:** native `lean --wasm` backend + optional language-core runtime in the browser.
**Is not:** the full Lean elaborator / emscripten `lean.js` editor stack (see `doc/make/emscripten.md`).
