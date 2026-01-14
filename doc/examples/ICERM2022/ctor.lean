import Lean

open Lean Meta

def ctor (mvarId : MVarId) (idx : Nat) : MetaM (List MVarId) := do
  /- Set `MetaM` context using `mvarId` -/
  mvarId.withContext do
    /- Fail if the metavariable is already assigned. -/
    mvarId.checkNotAssigned `ctor
    /- Retrieve the target type, instantiateMVars, and use `whnf`. -/
    let target ← mvarId.getType'
    let .const declName us := target.getAppFn
      | throwTacticEx `ctor mvarId "target is not an inductive datatype"
    let .inductInfo { ctors, .. } ← getConstInfo declName
      | throwTacticEx `ctor mvarId "target is not an inductive datatype"
    if idx = 0 then
      throwTacticEx `ctor mvarId "invalid index, it must be > 0"
    else if h : idx - 1 < ctors.length then
      mvarId.apply (.const ctors[idx - 1] us)
    else
      throwTacticEx `ctor mvarId "invalid index, inductive datatype has only {ctors.length} constructors"

open Elab Tactic

elab "ctor" idx:num : tactic =>
  liftMetaTactic (ctor · idx.getNat)

example (p : Prop) : p := by
  ctor 1 -- Error

example (h : q) : p ∨ q := by
  ctor 0 -- Error
  exact h

example (h : q) : p ∨ q := by
  ctor 3 -- Error
  exact h

example (h : q) : p ∨ q := by
  ctor 2
  exact h

example (h : q) : p ∨ q := by
  ctor 1
  exact h -- Error
