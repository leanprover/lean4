/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Cases
import Lean.Meta.Tactic.Rename
import Lean.Elab.SyntheticMVars
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.WF.TerminationHint

namespace Lean.Elab.WF
open Meta
open Term

private partial def unpackMutual (preDefs : Array PreDefinition) (mvarId : MVarId) (fvarId : FVarId) : TermElabM (Array (FVarId × MVarId)) := do
  let rec go (i : Nat) (mvarId : MVarId) (fvarId : FVarId) (result : Array (FVarId × MVarId)) : TermElabM (Array (FVarId × MVarId)) := do
    if i < preDefs.size - 1 then
      let #[s₁, s₂] ←  mvarId.cases fvarId | unreachable!
      go (i + 1) s₂.mvarId s₂.fields[0]!.fvarId! (result.push (s₁.fields[0]!.fvarId!, s₁.mvarId))
    else
      return result.push (fvarId, mvarId)
  go 0 mvarId fvarId #[]

private partial def unpackUnary (preDef : PreDefinition) (prefixSize : Nat) (mvarId : MVarId)
    (fvarId : FVarId) (extraParams : Nat) (element : TerminationBy) : TermElabM MVarId := do
  -- If elements.vars is ≤ extraParams, this is user-provided, and should be interpreted
  -- as left to right. Else it is provided by GuessLex, and may rename non-extra paramters as well.
  -- (Not pretty, but it works for now)
  let implicit_underscores :=
    if element.vars.size < extraParams then extraParams - element.vars.size else 0
  let varNames ← lambdaTelescope preDef.value fun xs _ => do
    let mut varNames ← xs.mapM fun x => x.fvarId!.getUserName
    if element.vars.size > varNames.size then
      throwErrorAt element.vars[varNames.size]! "too many variable names"
    for h : i in [:element.vars.size] do
      let varStx := element.vars[i]
      if let `($ident:ident) := varStx then
        let j := varNames.size - implicit_underscores - element.vars.size + i
        varNames := varNames.set! j ident.getId
    return varNames
  let mut mvarId := mvarId
  for localDecl in (← Term.getMVarDecl mvarId).lctx, varName in varNames[:prefixSize] do
    unless localDecl.userName == varName do
      mvarId ← mvarId.rename localDecl.fvarId varName
  let numPackedArgs := varNames.size - prefixSize
  let rec go (i : Nat) (mvarId : MVarId) (fvarId : FVarId) : TermElabM MVarId := do
    trace[Elab.definition.wf] "i: {i}, varNames: {varNames}, goal: {mvarId}"
    if i < numPackedArgs - 1 then
      let #[s] ← mvarId.cases fvarId #[{ varNames := [varNames[prefixSize + i]!] }] | unreachable!
      go (i+1) s.mvarId s.fields[1]!.fvarId!
    else
      mvarId.rename fvarId varNames.back
  go 0 mvarId fvarId

def elabWFRel (preDefs : Array PreDefinition) (unaryPreDefName : Name) (fixedPrefixSize : Nat)
    (argType : Expr) (extraParamss : Array Nat) (wf : TerminationWF) (k : Expr → TermElabM α) :
    TermElabM α := do
  let α := argType
  let u ← getLevel α
  let expectedType := mkApp (mkConst ``WellFoundedRelation [u]) α
  trace[Elab.definition.wf] "elabWFRel start: {(← mkFreshTypeMVar).mvarId!}"
  withDeclName unaryPreDefName do
    let mainMVarId := (← mkFreshExprSyntheticOpaqueMVar expectedType).mvarId!
    let [fMVarId, wfRelMVarId, _] ← mainMVarId.apply (← mkConstWithFreshMVarLevels ``invImage) | throwError "failed to apply 'invImage'"
    let (d, fMVarId) ← fMVarId.intro1
    let subgoals ← unpackMutual preDefs fMVarId d
    for (d, mvarId) in subgoals, extraParams in extraParamss, element in wf, preDef in preDefs do
      let mvarId ← unpackUnary preDef fixedPrefixSize mvarId d extraParams element
      mvarId.withContext do
        let value ← Term.withSynthesize <| elabTermEnsuringType element.body (← mvarId.getType)
        mvarId.assign value
    let wfRelVal ← synthInstance (← inferType (mkMVar wfRelMVarId))
    wfRelMVarId.assign wfRelVal
    k (← instantiateMVars (mkMVar mainMVarId))

end Lean.Elab.WF
