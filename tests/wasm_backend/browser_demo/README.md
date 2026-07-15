# WebAssembly browser demos

Two demos side by side:

| Page | Module | Runtime |
|---|---|---|
| [index.html](./index.html) | pure scalars | none |
| [core_rt.html](./core_rt.html) | multi-module + constructors/RC | language-core `libleanrt` |
| [ui.html](./ui.html) | typed fiber UI | language-core `libleanrt` |

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

# Typed UI, generated JS ABI bindings, and headless boot/click smoke test
./build_ui.sh
```

## Run

```bash
python3 -m http.server 8765
```

* <http://localhost:8765/> — scalar demo
* <http://localhost:8765/core_rt.html> — core runtime demo
* <http://localhost:8765/ui.html> — typed fiber UI

The UI crosses the JS/WASM boundary once per frame through a fixed-layout effect batch in linear
memory. `../UiAbi.lean` is the canonical opcode and handler contract;
`generate_ui_abi.py` emits the JavaScript constants and decoder plus TypeScript declarations.

The UI laboratory focuses on one persistent binary-search-tree application. Inserting a key creates
an immutable version by path copying. Selecting any earlier version before inserting creates a
branch, while stable node IDs and keyed elements show which subtrees are shared with the parent.
The pure model in `../PersistentTree.lean` separately tests version branching and node identity.

`build_ui.sh` validates the linked module and runs `ui_abi_smoke.mjs`, which boots the application,
inserts two keys, selects an earlier root, inserts a third key, and validates each effect batch.

## What this is (and is not)

**Is:** native `lean --wasm` backend + optional language-core runtime in the browser.
**Is not:** the full Lean elaborator / emscripten `lean.js` editor stack (see `doc/make/emscripten.md`).
