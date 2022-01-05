/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Eqns
import Lean.Util.CollectFVars
import Lean.Meta.Tactic.Split
import Lean.Meta.Tactic.Apply

namespace Lean.Elab.Eqns
open Meta

partial def expand : Expr → Expr
  | Expr.letE _ t v b _ => expand (b.instantiate1 v)
  | Expr.mdata _ b _    => expand b
  | e => e

def expandRHS? (mvarId : MVarId) : MetaM (Option MVarId) := do
  let target ← getMVarType' mvarId
  let some (_, lhs, rhs) ← target.eq? | return none
  unless rhs.isLet || rhs.isMData do return none
  return some (← replaceTargetDefEq mvarId (← mkEq lhs (expand rhs)))

def funext? (mvarId : MVarId) : MetaM (Option MVarId) := do
  let target ← getMVarType' mvarId
  let some (_, lhs, rhs) ← target.eq? | return none
  unless rhs.isLambda do return none
  commitWhenSome? do
    let [mvarId] ← apply mvarId (← mkConstWithFreshMVarLevels ``funext) | return none
    let (_, mvarId) ← intro1 mvarId
    return some mvarId

def simpMatch? (mvarId : MVarId) : MetaM (Option MVarId) := do
  let mvarId' ← Split.simpMatchTarget mvarId
  if mvarId != mvarId' then return some mvarId' else return none

def simpIf? (mvarId : MVarId) : MetaM (Option MVarId) := do
  let mvarId' ← simpIfTarget mvarId (useDecide := true)
  if mvarId != mvarId' then return some mvarId' else return none

structure Context where
  declNames : Array Name

/--
  Auxiliary method for `mkEqnTypes`. We should "keep going"/"processing" the goal
   `... |- f ... = rhs` at `mkEqnTypes` IF `rhs` contains a recursive application containing loose bound
  variables. We do that to make sure we can create an elimination principle for the recursive functions.

  Remark: we have considered using the same heuristic used in the `BRecOn` module.
  That is we would do case-analysis on the `match` application because the recursive
  argument (may) depend on it. We abandoned this approach because it was incompatible
  with the generation of induction principles.

  Remark: we could also always return `true` here, and split **all** match expressions on the `rhs`
  even if they are not relevant for the `brecOn` construction.
  TODO: reconsider this design decision in the future.
  Another possible design option is to "split" other control structures such as `if-then-else`.
-/
private def keepGoing (mvarId : MVarId) : ReaderT Context (StateRefT (Array Expr) MetaM) Bool := do
  let target ← getMVarType' mvarId
  let some (_, lhs, rhs) ← target.eq? | return false
  let ctx ← read
  return Option.isSome <| rhs.find? fun e => ctx.declNames.any e.isAppOf && e.hasLooseBVars

private def saveEqn (mvarId : MVarId) : StateRefT (Array Expr) MetaM Unit := withMVarContext mvarId do
  let target ← getMVarType' mvarId
  let fvarState := collectFVars {} target
  let fvarState ← (← getLCtx).foldrM (init := fvarState) fun decl fvarState => do
    if fvarState.fvarSet.contains decl.fvarId then
      collectFVars fvarState (← instantiateMVars decl.type)
    else
      fvarState
  let mut fvarIds ← sortFVarIds <| fvarState.fvarSet.toArray
  -- Include propositions that are not in fvarState.fvarSet, and only contains variables in
  for decl in (← getLCtx) do
    unless fvarState.fvarSet.contains decl.fvarId do
      if (← isProp decl.type) then
        let type ← instantiateMVars decl.type
        let missing? := type.find? fun e => e.isFVar && !fvarState.fvarSet.contains e.fvarId!
        if missing?.isNone then
          fvarIds := fvarIds.push decl.fvarId
  let type ← mkForallFVars (fvarIds.map mkFVar) target
  modify (·.push type)

partial def mkEqnTypes (declNames : Array Name) (mvarId : MVarId) : MetaM (Array Expr) := do
  let (_, eqnTypes) ← go mvarId |>.run { declNames } |>.run #[]
  return eqnTypes
where
  go (mvarId : MVarId) : ReaderT Context (StateRefT (Array Expr) MetaM) Unit := do
    if !(← keepGoing mvarId) then
      saveEqn mvarId
    else if let some mvarId ← expandRHS? mvarId then
      go mvarId
    else if let some mvarId ← funext? mvarId then
      go mvarId
    else if let some mvarId ← simpMatch? mvarId then
      go mvarId
    else if let some mvarIds ← splitTarget? mvarId then
      mvarIds.forM go
    else
      saveEqn mvarId

structure EqnsExtState where
  map : Std.PHashMap Name (Array Name) := {}
  deriving Inhabited

/- We generate the equations on demand, and do not save them on .olean files. -/
builtin_initialize eqnsExt : EnvExtension EqnsExtState ←
  registerEnvExtension (pure {})

/-- Create a "unique" base name for equations and splitter -/
def mkBaseNameFor (env : Environment) (declName : Name) : Name :=
  Lean.mkBaseNameFor env declName `_eq_1 `_eqns

/-- Try to close goal using `rfl` with smart unfolding turned off. -/
def tryURefl (mvarId : MVarId) : MetaM Bool :=
  withOptions (smartUnfolding.set . false) do
    try applyRefl mvarId; return true catch _ => return false

/-- Delta reduce the equation left-hand-side -/
def deltaLHS (mvarId : MVarId) : MetaM MVarId := withMVarContext mvarId do
  let target ← getMVarType' mvarId
  let some (_, lhs, rhs) ← target.eq? | throwTacticEx `deltaLHS mvarId "equality expected"
  let some lhs ← delta? lhs | throwTacticEx `deltaLHS mvarId "failed to delta reduce lhs"
  replaceTargetDefEq mvarId (← mkEq lhs rhs)

def deltaRHS? (mvarId : MVarId) (declName : Name) : MetaM (Option MVarId) := withMVarContext mvarId do
  let target ← getMVarType' mvarId
  let some (_, lhs, rhs) ← target.eq? | throwTacticEx `deltaRHS mvarId "equality expected"
  let some rhs ← delta? rhs.consumeMData (. == declName) | return none
  replaceTargetDefEq mvarId (← mkEq lhs rhs)

private partial def whnfAux (e : Expr) : MetaM Expr := do
  let e ← whnfR e
  match e with
  | Expr.proj _ _ s _ => e.updateProj! (← whnfAux s)
  | _ => e

/-- Apply `whnfR` to lhs, return `none` if `lhs` was not modified -/
def whnfReducibleLHS? (mvarId : MVarId) : MetaM (Option MVarId) := withMVarContext mvarId do
  let target ← getMVarType' mvarId
  let some (_, lhs, rhs) ← target.eq? | throwTacticEx `whnfReducibleLHS mvarId "equality expected"
  let lhs' ← whnfAux lhs
  if lhs' != lhs then
    return some (← replaceTargetDefEq mvarId (← mkEq lhs' rhs))
  else
    return none

def tryContradiction (mvarId : MVarId) : MetaM Bool := do
  try contradiction mvarId { genDiseq := true }; return true catch _ => return false

end Lean.Elab.Eqns
