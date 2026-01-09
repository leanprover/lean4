import Lean

/-!
This test file checks that delayed-assigned mvars are handled safely in `isDefEq` when in
`withAssignableSyntheticOpaque`.

Undesired behavior: if `?m.23` is delayed-assigned to `?a` and we naively replace `?m.23 [as]` with
`?a`, then we might expose unknown fvars if the type of `?a` depends on the new fvars in its
context.

To ensure we've fixed this, we check that `isDefEq` succeeds in these cases. `test e` logs the
result of `← withAssignableSyntheticOpaque <| isDefEq e (← getMainTarget)`. Whereas previously this
produced an "unknown fvar" error, here `isDefEq` should be able to succeed.
-/

open Lean Meta Elab Tactic in
elab "test " stx:term : tactic => withMainContext do
  let e ← elabTerm stx none
  logInfo m!"{← withAssignableSyntheticOpaque <| isDefEq e (← getMainTarget)}"
  check e

/-- A container that lets us include an arbitrary expression in a type. -/
inductive F {α} : α → Prop where | formal : F a

/-! ## Successful

In the following, even though the type of `?e` is not known and elaborates to another
delayed-assigned mvar with arguments. E.g. in `fun x => ?e`, `?e : ?m.1 x`, with `?m.1` delayed
assigned to `?A`. This is not an issue, as types are unified first: `x` can be cleared from the
context of `?A`, as `?A` has type `Sort ?u`, and `?A` can be unified with `Nat`. `x` no longer
appears in `Nat`, and so unification can proceed.

Previously, we would hit an unknown free variable and error out.
-/

/-- info: true -/
#guard_msgs in
theorem x : F (fun _ : Nat => 2) := by
  test F (fun _ : Nat => ?e)
  exact .formal

/-- info: true -/
#guard_msgs in
theorem xh : F (fun (x : Nat) (h : F x) => 2) := by
  test F (fun x h => ?e)
  exact .formal

/-- info: true -/
#guard_msgs in
theorem xhi : F (fun (x : Nat) (h : F x) [Decidable (F x)] => 2) := by
  test F (fun x h i => ?e)
  exact .formal

axiom f {α} (a : α) [Decidable (F a)] : Type

/-- info: true -/
#guard_msgs in
example : F (fun (x : Nat) {h : F x} [Decidable (F x)] (_ : f x) => 2) := by
  test F (fun x h i _ => ?e)
  exact .formal
