import Lean

open Lean Meta Elab Tactic in
elab "test " stx:term : tactic => withMainContext do
  let e ← elabTerm stx none
  logInfo m!"{← withAssignableSyntheticOpaque <| isDefEq e (← getMainTarget)}"
  check e

inductive F {α} : α → Prop where | formal : F a

theorem x : F (fun _ : Nat => 2) := by
  test F (fun _ : Nat => ?e)
  exact .formal

theorem xh : F (fun (x : Nat) (h : F x) => 2) := by
  test F (fun x h => ?e)
  exact .formal

theorem xhi : F (fun (x : Nat) (h : F x) [Decidable (F x)] => 2) := by
  test F (fun x h i => ?e)
  exact .formal

axiom f {α} (a : α) [Decidable (F a)] : Type

example : F (fun (x : Nat) {h : F x} [Decidable (F x)] (_ : f x) => 2) := by
  test F (fun x h i _ => ?e)
  exact .formal
