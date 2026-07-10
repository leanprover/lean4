module

/-!
Tests scalar comparisons, direct calls, and conditional WebAssembly lowering.
-/

def choose (x : UInt32) : UInt32 :=
  if x == 0 then 7 else 9

@[export lean_wasm_choose_zero]
def chooseZero : UInt32 := choose 0

@[export lean_wasm_choose_one]
def chooseOne : UInt32 := choose 1
