import Lean

/-!
Tests that a type class resolution query that gets stuck reports the metavariables it is stuck on,
and that the elaborator retries a stuck instance problem only once one of the metavariables it
depends on has been assigned.
-/

open Lean Meta Elab Term

class Foo (α : Type) where
  val : Nat
class Bar (α : Type) where
class Lvl (α : Sort u) (β : Type) where
instance : Foo Nat := ⟨0⟩
instance : Foo Int := ⟨1⟩
instance [Foo α] : Bar (List α) := ⟨⟩
instance : Lvl PUnit.{1} Nat := ⟨⟩

/-- Reports the blockers of the stuck query `type`. -/
def stuckOn (type : Expr) : MetaM Unit := do
  catchInternalId isDefEqStuckExceptionId
    (do logInfo m!"not stuck: {← synthInstance? type}")
    fun ex => do
      let (mvarIds, lmvarIds) := getIsDefEqStuckBlockers ex
      logInfo m!"stuck on {mvarIds.map mkMVar} {lmvarIds.map mkLevelMVar}"

/-! The blocker is the metavariable of the query that the unifier could not assign. -/

/-- info: stuck on [?a] [] -/
#guard_msgs in
run_meta do
  let a ← mkFreshExprMVar (mkSort .one) (userName := `a)
  stuckOn (mkApp (mkConst ``Foo) a)

/-- info: stuck on [?a] [] -/
#guard_msgs in
run_meta do
  let a ← mkFreshExprMVar (mkSort .one) (userName := `a)
  stuckOn (mkApp (mkConst ``Bar) (mkApp (mkConst ``List [.zero]) a))

/-! The blocker is a metavariable in the type of a local instance, which is not part of the query. -/

/-- info: stuck on [?a] [] -/
#guard_msgs in
run_meta do
  let a ← mkFreshExprMVar (mkSort .one) (userName := `a)
  withLocalDeclD `inst (mkApp (mkConst ``Foo) a) fun _ => do
    stuckOn (mkApp (mkConst ``Foo) (mkConst ``Nat))

/-! The blocker is a universe metavariable. -/

/-- info: stuck on [] [?u.1] -/
#guard_msgs in
run_meta do
  let u ← mkFreshLevelMVar
  withNewMCtxDepth do
    stuckOn (mkApp2 (mkConst ``Lvl [u]) (mkConst ``PUnit [u]) (mkConst ``Nat))

/-!
A pending instance problem is skipped while its dependencies are unassigned, even if other pending
problems make progress, and is retried once they are assigned.
-/

def needsFoo (α : Type) [Foo α] : Nat := Foo.val α

set_option pp.mvars.anonymous false in
/--
info: needsFoo Nat
---
trace: [Elab.postpone] resuming ?_
[Elab.postpone] skipped, still stuck
[Elab.postpone] not ready yet
[Elab.postpone] resuming ?_
[Elab.postpone] skipped, still stuck
[Elab.postpone] not ready yet
[Elab.postpone] resuming ?_
[Elab.postpone] skipped, still stuck
[Elab.postpone] not ready yet
[Elab.postpone] resuming ?_
[Elab.postpone] skipped, still stuck
[Elab.postpone] not ready yet
[Elab.postpone] resuming ?_
[Elab.postpone] skipped, still stuck
[Elab.postpone] not ready yet
[Elab.postpone] resuming ?_
[Elab.postpone] succeeded
[Elab.postpone] resuming ?_
[Elab.postpone] succeeded
[Elab.postpone] resuming ?_
[Elab.postpone] skipped, still stuck
[Elab.postpone] not ready yet
[Elab.postpone] resuming ?_
[Elab.postpone] succeeded
-/
#guard_msgs in
run_elab do
  let a ← mkFreshExprMVar (mkSort .one)
  let e ← elabTerm (← `(needsFoo $(← exprToSyntax a))) none
  withOptions (·.setBool `trace.Elab.postpone true) do
    synthesizeSyntheticMVars
    -- unrelated progress
    discard <| elabTerm (← `((1 + 2 : Nat))) none
    synthesizeSyntheticMVars
    a.mvarId!.assign (mkConst ``Nat)
    synthesizeSyntheticMVarsNoPostponing
  logInfo m!"{← instantiateMVars e}"

/-!
A problem stuck on a metavariable in the type of a local instance is retried when that metavariable
is assigned, although the query itself does not change.
-/

set_option trace.Elab.postpone true in
set_option pp.mvars.anonymous false in
/--
trace: [Elab.postpone] resuming ?_ x✝
[Elab.postpone] succeeded
-/
#guard_msgs in
example : Nat := (fun (_ : Foo _) => needsFoo Nat) instFooNat

/-! The stuck problem from lean4#2736 is still solved once its instance arguments are known. -/

class RightDistribClass (R : Type) [Mul R] [Add R] : Prop where
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

class MulOneClass' (α : Type) extends Mul α, One α

axiom add_one_mul' [Add α] [MulOneClass' α] [RightDistribClass α] (a b : α) :
    (a + 1) * b = a * b + b

instance : MulOneClass' Nat := {}
instance : RightDistribClass Nat := ⟨Nat.add_mul⟩

example (a b : Nat) : (a + 1) * b = a * b + b := add_one_mul' a b
example (a b : Nat) : (a + 1) * b = a * b + b := by rw [add_one_mul']
