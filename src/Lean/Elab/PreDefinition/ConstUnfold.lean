/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
prelude
import Lean.Meta.Eqns
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Rfl
import Lean.Meta.Tactic.Intro
import Lean.Meta.Tactic.Apply

namespace Lean.Meta

/-- Try to close goal using `rfl` with smart unfolding turned off. -/
def tryURefl (mvarId : MVarId) : MetaM Bool :=
  withOptions (smartUnfolding.set · false) do
    try mvarId.refl; return true catch _ => return false

def funext (mvarId : MVarId) : MetaM MVarId := do
  let [mvarId] ← mvarId.apply (← mkConstWithFreshMVarLevels ``funext)
    | throwError "could not apply funext\n{mvarId}"
  let (_, mvarId) ← mvarId.intro1
  return mvarId

/--
Returns the "const unfold" theorem (`f.unfold`) for the given declaration.
This is not extensible, and always builds on the unfold theorem (`f.eq_def`).
-/
def getConstUnfoldEqnFor? (declName : Name) : MetaM (Option Name) := do
  let some unfoldEqnName ← getUnfoldEqnFor? (nonRec := true) declName | return none
  let info ← getConstInfo unfoldEqnName
  let (type, arity) ← forallTelescope info.type fun xs eq => do
    let some (_, lhs, rhs) := eq.eq? | throwError "Unexpected unfold theorem type {info.type}"
    unless lhs.getAppFn.isConstOf declName do
     throwError "Unexpected unfold theorem type {info.type}"
    unless lhs.getAppArgs == xs do
     throwError "Unexpected unfold theorem type {info.type}"
    let type ← mkEq lhs.getAppFn (← mkLambdaFVars xs rhs)
    return (type, xs.size)
  let value ← withNewMCtxDepth do
    let main ← mkFreshExprSyntheticOpaqueMVar type
    let mut goal := main.mvarId!
    unless (← tryURefl goal) do -- try to make a rfl lemma if possible
      for _ in [:arity] do
        goal ← funext goal
      let [] ← goal.apply (.const unfoldEqnName (info.levelParams.map mkLevelParam))
        | throwError "Could no close goal {← goal.getType'}"

    instantiateMVars main
  let name := .str declName constUnfoldThmSuffix
  addDecl <| Declaration.thmDecl {
    name, type, value
    levelParams := info.levelParams
  }
  return some name


builtin_initialize
  registerReservedNameAction fun name => do
    let .str p s := name | return false
    unless (← getEnv).isSafeDefinition p do return false
    if s == constUnfoldThmSuffix then
      return (← MetaM.run' <| getConstUnfoldEqnFor? p).isSome
    return false

end Lean.Meta
