import Lean
set_option warn.sorry false

/-!
Tests for `Sym.simp` on target terms containing unassigned metavariables.
Unassigned metavariables in the target must be treated as opaque atoms: a pattern
variable can be bound to one, but the matcher must never assign it, and
`Theorem.rewrite` must not confuse it with an undischarged hypothesis.
-/

open Lean Meta Sym Simp

opaque p : (Nat → Prop) → Nat → Prop
theorem p_apply (F : Nat → Prop) (x : Nat) : p F x = F x := sorry

-- Rewriting fires on a target whose operand is an unassigned metavariable `?F`:
-- the goal after `rotate_left` is `p ?F s = ?F s`.
example (Q : Nat → Prop) (s : Nat) : ∃ F : Nat → Prop, (p F s) = (F s) := by
  refine ⟨?_, ?_⟩
  rotate_left
  sym => simp [p_apply]
  exact Q

-- `Theorem.rewrite` on `p ?F s` steps to `?F s`, binding the pattern variable to the
-- metavariable without treating its type as a side condition to discharge.
/-- info: step: ?F s -/
#guard_msgs in
run_meta SymM.run do
  let natProp := mkForall `x .default (mkConst ``Nat) (mkSort .zero)
  withLocalDeclD `s (mkConst ``Nat) fun s => do
    let F ← mkFreshExprMVar natProp (userName := `F)
    let e ← shareCommon (mkApp2 (mkConst ``p) F s)
    let thm ← mkTheoremFromDecl ``p_apply
    let r ← SimpM.run' (thm.rewrite e)
    match r with
    | .step e' _ _ _ => logInfo m!"step: {e'}"
    | _ => logInfo "rfl"

-- A nonlinear pattern must NOT fire by unifying a target metavariable: `Nat.sub_self`
-- on `?x - 5` would produce a step valid only under `?x := 5`, an assignment that is
-- discarded by `withNewMCtxDepth`. The match must fail instead.
/-- info: rfl -/
#guard_msgs in
run_meta SymM.run do
  let x ← mkFreshExprMVar (mkConst ``Nat) (userName := `x)
  let e ← shareCommon (← mkAppM ``HSub.hSub #[x, mkNatLit 5])
  let thm ← mkTheoremFromDecl ``Nat.sub_self
  let r ← SimpM.run' (thm.rewrite e)
  match r with
  | .step e' _ _ _ => logInfo m!"step: {e'}"
  | _ => logInfo "rfl"

-- The metavariable must remain unassigned after a failed nonlinear match attempt.
/-- info: assigned: false -/
#guard_msgs in
run_meta SymM.run do
  let x ← mkFreshExprMVar (mkConst ``Nat) (userName := `x)
  let e ← shareCommon (← mkAppM ``HSub.hSub #[x, mkNatLit 5])
  let thm ← mkTheoremFromDecl ``Nat.sub_self
  discard <| SimpM.run' (thm.rewrite e)
  logInfo m!"assigned: {← x.mvarId!.isAssigned}"
