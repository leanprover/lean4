/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Joachim Breitner
-/
prelude
import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Split
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.Eqns
import Lean.Meta.ArgsPacker.Basic
import Init.Data.Array.Basic

namespace Lean.Elab.Nonrec
open Meta
open Eqns

/--
Simple, coarse-grained equation theorem for nonrecursive definitions.
-/
private def mkSimpleEqThm (declName : Name) (suffix := Name.mkSimple unfoldThmSuffix) : MetaM (Option Name) := do
  if let some (.defnInfo info) := (← getEnv).find? declName then
    lambdaTelescope (cleanupAnnotations := true) info.value fun xs body => do
      let lhs := mkAppN (mkConst info.name <| info.levelParams.map mkLevelParam) xs
      let type  ← mkForallFVars xs (← mkEq lhs body)
      let value ← mkLambdaFVars xs (← mkEqRefl lhs)
      let name := declName ++ suffix
      addDecl <| Declaration.thmDecl {
        name, type, value
        levelParams := info.levelParams
      }
      return some name
  else
    return none

private partial def mkProof (declName : Name) (type : Expr) : MetaM Expr := do
  trace[Elab.definition.eqns] "proving: {type}"
  withNewMCtxDepth do
    let main ← mkFreshExprSyntheticOpaqueMVar type
    let (_, mvarId) ← main.mvarId!.intros
    let rec go (mvarId : MVarId) : MetaM Unit := do
      trace[Elab.definition.eqns] "step\n{MessageData.ofGoal mvarId}"
      if ← withAtLeastTransparency .all (tryURefl mvarId) then
        return ()
      else if (← tryContradiction mvarId) then
        return ()
      else if let some mvarId ← simpMatch? mvarId then
        go mvarId
      else if let some mvarId ← simpIf? mvarId then
        go mvarId
      else if let some mvarId ← whnfReducibleLHS? mvarId then
        go mvarId
      else match (← simpTargetStar mvarId { config.dsimp := false } (simprocs := {})).1 with
        | TacticResultCNM.closed => return ()
        | TacticResultCNM.modified mvarId => go mvarId
        | TacticResultCNM.noChange =>
          if let some mvarIds ← casesOnStuckLHS? mvarId then
            mvarIds.forM go
          else if let some mvarIds ← splitTarget? mvarId then
            mvarIds.forM go
          else
            throwError "failed to generate equational theorem for '{declName}'\n{MessageData.ofGoal mvarId}"

    -- Try rfl before deltaLHS to avoid `id` checkpoints in the proof, which would make
    -- the lemma ineligible for dsimp
    unless ← withAtLeastTransparency .all (tryURefl mvarId) do
      go (← deltaLHS mvarId)
    instantiateMVars main

def mkEqns (declName : Name) (info : DefinitionVal) : MetaM (Array Name) :=
  withOptions (tactic.hygienic.set · false) do
  let baseName := declName
  let eqnTypes ← withNewMCtxDepth <| lambdaTelescope (cleanupAnnotations := true) info.value fun xs body => do
    let us := info.levelParams.map mkLevelParam
    let target ← mkEq (mkAppN (Lean.mkConst declName us) xs) body
    let goal ← mkFreshExprSyntheticOpaqueMVar target
    withReducible do
      mkEqnTypes #[] goal.mvarId!
  let mut thmNames := #[]
  for h : i in [: eqnTypes.size] do
    let type := eqnTypes[i]
    trace[Elab.definition.eqns] "eqnType[{i}]: {eqnTypes[i]}"
    let name := (Name.str baseName eqnThmSuffixBase).appendIndexAfter (i+1)
    thmNames := thmNames.push name
    let value ← mkProof declName type
    let (type, value) ← removeUnusedEqnHypotheses type value
    addDecl <| Declaration.thmDecl {
      name, type, value
      levelParams := info.levelParams
    }
  return thmNames

def getEqnsFor? (declName : Name) : MetaM (Option (Array Name)) := do
  if (← isRecursiveDefinition declName) then
    return none
  if let some (.defnInfo info) := (← getEnv).find? declName then
    if backward.eqns.nonrecursive.get (← getOptions) then
      mkEqns declName info
    else
      let o ← mkSimpleEqThm declName
      return o.map (#[·])
  else
    return none

builtin_initialize
  registerGetEqnsFn getEqnsFor?

end Lean.Elab.Nonrec
