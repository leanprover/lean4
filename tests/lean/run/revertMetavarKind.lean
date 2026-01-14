import Lean.Meta

open Lean Elab Tactic

example (n : Nat) : n = n := by
  revert n
  run_tac do
    guard (← getMainDecl).kind.isSyntheticOpaque
  intro n
  rfl
