/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module


prelude
public import Lean.Meta.Basic
import Lean.Meta.Tactic.Split
import Lean.Meta.Tactic.Refl
import Lean.Meta.Tactic.Delta
import Lean.Meta.Tactic.SplitIf
import Lean.Meta.Tactic.Contradiction

/-!
This module contains helpers useful to prove unfolding and/or equational theorems.
-/

namespace Lean.Elab.Eqns
open Meta

public def simpMatch? (mvarId : MVarId) : MetaM (Option MVarId) := do
  let mvarId' ← Split.simpMatchTarget mvarId
  if mvarId != mvarId' then return some mvarId' else return none

/--
Simplify `if-then-expression`s in the goal target.
If `useNewSemantics` is `true`, the flag `backward.split` is ignored.
-/
public def simpIf? (mvarId : MVarId) (useNewSemantics := false) : MetaM (Option MVarId) := do
  let mvarId' ← simpIfTarget mvarId (useDecide := true) (useNewSemantics := useNewSemantics)
  if mvarId != mvarId' then return some mvarId' else return none

/-- Try to close goal using `rfl` with smart unfolding turned off. -/
public def tryURefl (mvarId : MVarId) : MetaM Bool :=
  withOptions (smartUnfolding.set · false) do
    try mvarId.refl; return true catch _ => return false

/-- Delta reduce the equation left-hand-side -/
public def deltaLHS (mvarId : MVarId) : MetaM MVarId := mvarId.withContext do
  let target ← mvarId.getType'
  let some (_, lhs, rhs) := target.eq? | throwTacticEx `deltaLHS mvarId "equality expected"
  let some lhs ← delta? lhs | throwTacticEx `deltaLHS mvarId "failed to delta reduce lhs"
  mvarId.replaceTargetDefEq (← mkEq lhs rhs)

public def tryContradiction (mvarId : MVarId) : MetaM Bool := do
  mvarId.contradictionCore { genDiseq := true }

partial def whnfAux (e : Expr) : MetaM Expr := do
  let e ← whnfI e -- Must reduce instances too, otherwise it will not be able to reduce `(Nat.rec ... ... (OfNat.ofNat 0))`
  let f := e.getAppFn
  match f with
  | .proj _ _ s => return mkAppN (f.updateProj! (← whnfAux s)) e.getAppArgs
  | _ => return e

/-- Apply `whnfR` to lhs, return `none` if `lhs` was not modified -/
public def whnfReducibleLHS? (mvarId : MVarId) : MetaM (Option MVarId) := mvarId.withContext do
  let target ← mvarId.getType'
  let some (_, lhs, rhs) := target.eq? | return none
  let lhs' ← whnfAux lhs
  if lhs' != lhs then
    return some (← mvarId.replaceTargetDefEq (← mkEq lhs' rhs))
  else
    return none

end Lean.Elab.Eqns
