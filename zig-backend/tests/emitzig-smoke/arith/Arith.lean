module

/-! EmitZig smoke test covering small `Nat` and `UInt32` arithmetic. -/

def main : IO Unit := do
  let natPart : Nat := 17 + 25
  let wordPart : UInt32 := 5 + 7
  let total : Nat := natPart + wordPart.toNat
  IO.println (toString total)
