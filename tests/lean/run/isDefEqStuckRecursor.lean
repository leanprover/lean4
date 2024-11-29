import Lean

noncomputable def foo (n : Nat) : Nat :=
  Decidable.rec (fun _ => 10) (fun _ => n) (Classical.propDecidable True)

open Lean Meta

/-
in `isDefEq`, inside `tryUnificationHints`, inside `DiscrTree.getMatch`,
an `isDefEqStuck` exception used to be thrown.
-/
run_meta do
  let n ← mkFreshExprMVar (Expr.const ``Nat [])
  let e := mkApp (.const ``foo []) n
  withConfig (fun cfg => { cfg with isDefEqStuckEx := true }) do
  guard !(← isDefEq e (.const ``Nat.zero []))
