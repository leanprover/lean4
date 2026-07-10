module

/-!
Tests wasm32 persistent arrays with boxed scalar elements.
-/

@[noinline] def pairArray (x y : UInt32) : Array UInt32 :=
  #[x, y]

@[export lean_wasm_array_sum]
def arraySum (x y : UInt32) : UInt32 :=
  let values := pairArray x y
  values.getD 0 0 + values.getD 1 0
