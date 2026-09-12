import Lean
/-!
Tests that `MVarId.reparametrize` rejects a result that refers to erased declarations. Only `fold` can
smuggle such a reference past the dependency guards, so the test uses a fold that reintroduces the
replaced variable itself. The result is type correct in the old context but not in the new one.
-/

open Lean Meta Elab Tactic

structure Wrap where
  inner : Nat

/-- Replaces `a : Nat` by `y.inner`, folding `P y.inner` back to `P a` with the erased `a`. -/
elab "bad_fold" : tactic => withMainContext do
  let some a := (← getLCtx).findFromUserName? `a | throwError "no `a`"
  let some P := (← getLCtx).findFromUserName? `P | throwError "no `P`"
  let r? ← withLocalDeclD `y (mkConst ``Wrap) fun y => do
    let yInner := mkApp (mkConst ``Wrap.inner) y
    let fold e := if e == mkApp P.toExpr yInner then some (mkApp P.toExpr a.toExpr) else none
    Reparametrize.reparametrize (← getMainGoal) a.fvarId y.fvarId! yInner
      (mkApp (mkConst ``Wrap.mk) a.toExpr) fold
  match r? with
  | none => logInfo "rejected"
  | some r => replaceMainGoal [r.mvarId]

/-- info: rejected -/
#guard_msgs in
example (a : Nat) (P : Nat → Prop) (h : P a) : P a := by
  bad_fold
  exact h
