/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.CollectFVars
import Lean.Meta.Tactic.Clear

namespace Lean.Meta

/--
  Auxiliary tactic for cleaning the local context. It removes local declarations (aka hypotheses) that are *not* relevant.
  We say a variable `x` is "relevant" if
  - It occurs in the target type, or
  - There is a relevant variable `y` that depends on `x`, or
  - The type of `x` is a proposition and it depends on a relevant variable `y`.
-/
partial def cleanup (mvarId : MVarId) : MetaM MVarId := do
  withMVarContext mvarId do
    checkNotAssigned mvarId `cleanup
    let used ← collectUsed |>.run' (false, {})
    let mut lctx ← getLCtx
    for localDecl in lctx do
      unless used.contains localDecl.fvarId do
        lctx := lctx.erase localDecl.fvarId
    let localInsts := (← getLocalInstances).filter fun inst => used.contains inst.fvar.fvarId!
    let mvarNew ← mkFreshExprMVarAt lctx localInsts (← instantiateMVars (← getMVarType mvarId)) MetavarKind.syntheticOpaque (← getMVarTag mvarId)
    assignExprMVar mvarId mvarNew
    return mvarNew.mvarId!
where
  addUsedFVars (e : Expr) : StateRefT (Bool × FVarIdSet) MetaM Unit := do
    let (_, s) ← (← instantiateMVars e).collectFVars |>.run {}
    for fvarId in s.fvarSet do
      addUsedFVar fvarId

  addDeps (fvarId : FVarId) : StateRefT (Bool × FVarIdSet) MetaM Unit := do
    let localDecl ← getLocalDecl fvarId
    addUsedFVars localDecl.type
    if let some val := localDecl.value? then
      addUsedFVars val

  addUsedFVar (fvarId : FVarId) : StateRefT (Bool × FVarIdSet) MetaM Unit := do
    unless (← get).2.contains fvarId do
      modify fun (_, s) => (true, s.insert fvarId)
      addDeps fvarId

  /- We include `p` in the used-set, if `p` is a proposition that contains a `x` that is in the used-set. -/
  collectPropsStep : StateRefT (Bool × FVarIdSet) MetaM Unit := do
    let usedSet := (← get).2
    for localDecl in (← getLCtx) do
      if (← isProp localDecl.type) then
        if (← dependsOnPred localDecl.type usedSet.contains) then
          addUsedFVar localDecl.fvarId

  collectProps : StateRefT (Bool × FVarIdSet) MetaM Unit := do
    modify fun s => (false, s.2)
    collectPropsStep
    if (← get).1 then
      collectProps

  collectUsed : StateRefT (Bool × FVarIdSet) MetaM FVarIdSet := do
    addUsedFVars (← instantiateMVars (← getMVarType mvarId))
    collectProps
    return (← get).2

end Lean.Meta
