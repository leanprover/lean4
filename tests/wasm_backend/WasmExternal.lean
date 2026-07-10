module

/-!
Provides an exported scalar function for the cross-object WebAssembly test.
-/

@[export lean_wasm_external_add_one]
public def wasmExternalAddOne (x : UInt32) : UInt32 := x + 1
