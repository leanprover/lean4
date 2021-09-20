# Compiling lean.js via Emscripten

First install Emscripten via your distribution's package manager or [download and install it](https://kripken.github.io/emscripten-site/docs/getting_started/downloads.html) yourself. Then build asm.js and WebAssembly binaries using

```bash
mkdir -p build/emscripten
cd build/emscripten
emconfigure cmake ../../src -DCMAKE_BUILD_TYPE=Emscripten
make lean_js_js lean_js_wasm
```

This will produce files `lean_js_js.js`, `lean_js_wasm.js`, and `lean_js_wasm.wasm` in `shell/`, which you can e.g. copy to the `dist/` directory in [lean-web-editor](https://github.com/leanprover/lean-web-editor) instead of calling `./fetch_lean_js.sh` there.
