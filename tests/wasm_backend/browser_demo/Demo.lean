module

/-!
Pure-scalar exports for the WebAssembly browser demo (no runtime imports).
-/

@[export lean_wasm_demo_add]
def demoAdd (x y : UInt32) : UInt32 := x + y

@[export lean_wasm_demo_answer]
def demoAnswer : UInt32 := 42

@[export lean_wasm_demo_choose]
def demoChoose (x : UInt32) : UInt32 :=
  if x == 0 then 7 else 9
