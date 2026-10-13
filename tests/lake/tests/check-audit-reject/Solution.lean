-- `lake check` re-checks everything in scope, so import only what `run_elab` and `addDecl` need.
import Lean.Elab.BuiltinEvalCommand
import Lean.AddDecl

open Lean

unsafe def badNatUnsafe : Nat := unsafeCast (-4294967296 : Int)

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
  have truly_marvelous_0 : ¬badNat ≤ 9223372036854775807 := by decide
  have truly_marvelous_1 : ¬9223372036854775807 < badNat := by decide
  omega
