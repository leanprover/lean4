import Lean

open Lean

-- A big `Nat` (a `ByteArray` of 32-bit digits) with a leading zero digit, which the runtime
-- compares by digit count against single-digit and by digits against two-digit numbers.
unsafe def badNatUnsafe : Nat := unsafeCast (ByteArray.mk #[5, 0, 0, 0, 0, 0, 0, 0])

@[implemented_by badNatUnsafe] opaque badNatVal : Nat

run_elab
  addDecl <| .defnDecl {
    name        := .str .anonymous "badNat"
    levelParams := []
    type        := .const ``Nat []
    value       := .lit <| .natVal badNatVal
    hints       := .opaque
    safety      := .safe
  }

theorem boom : False := by
  have truly_marvelous_0 : ¬badNat ≤ 4294967295 := by decide
  have truly_marvelous_1 : badNat < 4294967296 := by decide
  omega
