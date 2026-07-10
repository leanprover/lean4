# Compiling Lean via Emscripten

This path builds **Lean itself** (compiler + elaborator) as a WebAssembly /
JavaScript package for embedding (historically used by web editors). It is
separate from the **language-core wasm32 backend** (`lean --wasm=`,
`libleanrt` for pure programs).

## Status (2026)

| Piece | Status |
|---|---|
| CMake `Emscripten` system name / flags | Present in `src/CMakeLists.txt` |
| CI “Web Assembly” matrix job | **Commented out** in `.github/workflows/ci.yml` |
| `src/shell/lean_js.cpp` | **Lean 3 API** (dead; does not compile against Lean 4) |
| Modern replacement | Use emscripten to build stage1 `lean` as MAIN_MODULE, or drive the new `--wasm` + core-runtime path for **user programs** |

Reviving a full “Lean in the browser” editor stack means either:

1. **Re-enable emscripten stage1 build** of the Lean binary (heavy; needs
   filesystem / nodefs / library tree), **or**
2. Prefer the **native wasm backend + language-core runtime** for running
   compiled Lean programs, and keep the elaborator native/server-side.

## Prerequisites

Install [Emscripten](https://emscripten.org/docs/getting_started/downloads.html)
(emsdk) and activate it (`emcc` on `PATH`). CI historically pinned **3.1.44**;
newer emsdk may need flag tweaks.

On macOS with Homebrew:

```bash
brew install emscripten
```

## Configure and build (experimental)

From the repository root, after a normal native stage0/stage1 is available for
bootstrapping oleans:

```bash
mkdir -p build/emscripten
cd build/emscripten

# Toolchain file from your emsdk install, e.g.:
#   $EMSDK/upstream/emscripten/cmake/Modules/Platform/Emscripten.cmake
emcmake cmake ../../src \
  -DCMAKE_BUILD_TYPE=Release \
  -DUSE_GMP=OFF \
  -DMMAP=OFF \
  -DLEAN_INSTALL_SUFFIX=-wasm32

cmake --build . --target lean -j"$(sysctl -n hw.logicalcpu 2>/dev/null || nproc)"
```

Notes:

* Stage0 should stay **native** (see commented CI job: 32-bit stage0 + emscripten
  stage1). Cross-compiling everything under emscripten is much harder.
* Lake / LeanChecker are skipped under Emscripten in CMake.
* `lean_js.cpp` is not a Lean 4 target; do not expect `lean_js_js` / `lean_js_wasm`
  product names from Lean 3 docs until a new export shell is written.

## Helper script

```bash
script/build_emscripten.sh
```

This configures `build/emscripten` if needed and builds `lean`. Failures are
expected until the matrix job is fully revalidated; capture the log for porting.

## Related: language-core WASI runtime

For **compiled pure Lean programs** (not the elaborator):

```bash
export WASI_SDK_PATH=/path/to/wasi-sdk
script/build_wasm_runtime.sh
# then: lean --wasm=foo.wasm Foo.lean
#       leanc --target=wasm32-wasip1 -o foo.linked.wasm foo.wasm
```

See `tests/wasm_backend/` and `tests/wasm_backend/browser_demo/`.
