module

/-!
Closed/large constants for WASM backend completeness (nullary closed helpers + scalar lit).
-/

def closedBig : Nat := 12345678901234567890

@[export lean_wasm_closed_add]
def closedAdd (n : Nat) : Nat :=
  n + closedBig

@[export lean_wasm_closed_lit]
def closedLit : UInt32 := 99
