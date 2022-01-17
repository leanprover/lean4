/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Rename
import Lean.Meta.Tactic.Intro
import Lean.Elab.SyntheticMVars
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.WF.TerminationHint

namespace Lean.Elab.WF
open Meta
open Term

private def getRefFromElems (elems : Array TerminationByElement) : Syntax := Id.run do
  for elem in elems do
    if !elem.implicit then
      return elem.ref
  return elems[0].ref

private partial def unpackMutual (preDefs : Array PreDefinition) (mvarId : MVarId) (fvarId : FVarId) : TermElabM (Array (FVarId × MVarId)) := do
  let rec go (i : Nat) (mvarId : MVarId) (fvarId : FVarId) (result : Array (FVarId × MVarId)) : TermElabM (Array (FVarId × MVarId)) := do
    if i < preDefs.size - 1 then
      let #[s₁, s₂] ← cases mvarId fvarId | unreachable!
      go (i + 1) s₂.mvarId s₂.fields[0].fvarId! (result.push (s₁.fields[0].fvarId!, s₁.mvarId))
    else
      return result.push (fvarId, mvarId)
  go 0 mvarId fvarId #[]

private partial def unpackUnary (preDef : PreDefinition) (mvarId : MVarId) (fvarId : FVarId) (element : TerminationByElement) : TermElabM MVarId := do
  let varNames ← lambdaTelescope preDef.value fun xs body => do
    let mut varNames ← xs.mapM fun x => return (← getLocalDecl x.fvarId!).userName
    if element.vars.size > varNames.size then
      throwErrorAt element.vars[varNames.size] "too many variable names"
    for i in [:element.vars.size] do
      let varStx := element.vars[i]
      if varStx.isIdent then
        varNames := varNames.set! (varNames.size - element.vars.size + i) varStx.getId
    return varNames
  let rec go (i : Nat) (mvarId : MVarId) (fvarId : FVarId) : TermElabM MVarId := do
    if i < varNames.size - 1 then
      let #[s] ← cases mvarId fvarId #[{ varNames := [varNames[i]] }] | unreachable!
      go (i+1) s.mvarId s.fields[1].fvarId!
    else
      rename mvarId fvarId varNames.back
  go 0 mvarId fvarId

def elabWFRel (preDefs : Array PreDefinition) (unaryPreDef : PreDefinition) (wf? : Option TerminationWF) : TermElabM Expr := do
  let α := unaryPreDef.type.bindingDomain!
  let u ← getLevel α
  let expectedType := mkApp (mkConst ``WellFoundedRelation [u]) α
  match wf? with
  | some (TerminationWF.core wfStx) => withDeclName unaryPreDef.declName do
      let wfRel ← instantiateMVars (← withSynthesize <| elabTermEnsuringType wfStx expectedType)
      let pendingMVarIds ← getMVars wfRel
      discard <| logUnassignedUsingErrorInfos pendingMVarIds
      return wfRel
  | some (TerminationWF.ext elements) => withDeclName unaryPreDef.declName <| withRef (getRefFromElems elements) do
    let mainMVarId := (← mkFreshExprSyntheticOpaqueMVar expectedType).mvarId!
    let [fMVarId, wfRelMVarId, _] ← apply mainMVarId (← mkConstWithFreshMVarLevels ``invImage) | throwError "failed to apply 'invImage'"
    let (d, fMVarId) ← intro1 fMVarId
    let subgoals ← unpackMutual preDefs fMVarId d
    for (d, mvarId) in subgoals, element in elements, preDef in preDefs do
      let mvarId ← unpackUnary preDef mvarId d element
      withMVarContext mvarId do
        let value ← Term.withSynthesize <| elabTermEnsuringType element.body (← getMVarType mvarId)
        assignExprMVar mvarId value
    let wfRelVal ← synthInstance (← inferType (mkMVar wfRelMVarId))
    assignExprMVar wfRelMVarId wfRelVal
    instantiateMVars (mkMVar mainMVarId)
  | none =>
    -- TODO: try to synthesize some default relation
    throwError "'termination_by' modifier missing"

end Lean.Elab.WF
