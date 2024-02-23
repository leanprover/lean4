import Lean

open Lean Meta Elab Tactic in
elab "test " stx:term : tactic => withMainContext do
  let e ← elabTerm stx none
  discard <| withAssignableSyntheticOpaque <| isDefEq e (← getMainTarget)

axiom F {α} : α → Prop

theorem x : F (fun _ : Nat => 2) := by
  test F (fun _ : Nat => ?e)
  admit

theorem xh : F (fun (x : Nat) (h : F x) => 2) := by
  test F (fun x h => ?e)
  admit
