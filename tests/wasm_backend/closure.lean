module

/-!
Tests wasm32 closure allocation, fixed arguments, and indirect application.
-/

@[noinline] def applyFn (f : UInt32 → UInt32) (x : UInt32) : UInt32 :=
  f x

@[export lean_wasm_closure]
def closure (base x : UInt32) : UInt32 :=
  applyFn (fun y => base + y) x
