module

/-!
Tests direct scalar WebAssembly lowering and exported function execution.
-/

@[export lean_wasm_answer]
def answer : UInt32 := 42

@[export lean_wasm_add]
def add (x y : UInt32) : UInt32 := x + y
