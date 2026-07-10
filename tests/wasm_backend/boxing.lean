module

/-!
Tests wasm32 boxing and unboxing through a list constructor and projection.
-/

@[noinline] def first (xs : List UInt32) : UInt32 :=
  xs.headD 0

@[export lean_wasm_box_roundtrip]
def boxRoundtrip (x : UInt32) : UInt32 :=
  first [x]
