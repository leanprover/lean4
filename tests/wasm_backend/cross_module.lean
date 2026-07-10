module

import WasmExternal

/-!
Tests an undefined Lean function import resolved from another WebAssembly object.
-/

@[export lean_wasm_cross_module]
def callExternal (x : UInt32) : UInt32 :=
  wasmExternalAddOne x
