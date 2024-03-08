import Lean

/-!
This test file checks that delayed-assigned mvars are handled safely in `isDefEq` when in
`withAssignableSyntheticOpaque`.

Undesired behavior: if `?m.23` is delayed-assigned to `?a` and we naively replace `?m.23 [as]` with
`?a`, then we might expose unknown fvars if the type of `?a` depends on the new fvars in its
context. Notably, the type depends on these new fvars whenever it is not specified, e.g. when
elaborating `fun x => ?a`.

To ensure we've fixed this, we check that `isDefEq` fails in these cases. `test e` logs the result
of `← withAssignableSyntheticOpaque <| isDefEq e (← getMainTarget)`. Whereas previously this
produced an "unknown fvar" error, here `isDefEq` should detect that the type of `e` is not
well-formed in the new context and fail, logging `false`.
-/

open Lean Meta Elab Tactic in
elab "test " stx:term : tactic => withMainContext do
  let e ← elabTerm stx none
  logInfo m!"{← withAssignableSyntheticOpaque <| isDefEq e (← getMainTarget)}"
  check e

/-- A container that lets us include an arbitrary expression in a type. -/
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
