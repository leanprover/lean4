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

private def getRefFromElems (elems : Array TerminationByElement) : Syntax := Id.run do
  for elem in elems do
    if !elem.implicit then
      return elem.ref
  return elems[0]!.ref

private partial def unpackMutual (preDefs : Array PreDefinition) (mvarId : MVarId) (fvarId : FVarId) : TermElabM (Array (FVarId × MVarId)) := do
  let rec go (i : Nat) (mvarId : MVarId) (fvarId : FVarId) (result : Array (FVarId × MVarId)) : TermElabM (Array (FVarId × MVarId)) := do
    if i < preDefs.size - 1 then
      let #[s₁, s₂] ←  mvarId.cases fvarId | unreachable!
      go (i + 1) s₂.mvarId s₂.fields[0]!.fvarId! (result.push (s₁.fields[0]!.fvarId!, s₁.mvarId))
    else
      return result.push (fvarId, mvarId)
  go 0 mvarId fvarId #[]

private partial def unpackUnary (preDef : PreDefinition) (prefixSize : Nat) (mvarId : MVarId) (fvarId : FVarId) (element : TerminationByElement) : TermElabM MVarId := do
  let varNames ← lambdaTelescope preDef.value fun xs _ => do
    let mut varNames ← xs.mapM fun x => x.fvarId!.getUserName
    if element.vars.size > varNames.size then
      throwErrorAt element.vars[varNames.size]! "too many variable names"
    for i in [:element.vars.size] do
      let varStx := element.vars[i]!
      if varStx.isIdent then
        varNames := varNames.set! (varNames.size - element.vars.size + i) varStx.getId
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

def getNumCandidateArgs (fixedPrefixSize : Nat) (preDefs : Array PreDefinition) : MetaM (Array Nat) := do
  preDefs.mapM fun preDef =>
    lambdaTelescope preDef.value fun xs _ =>
      return xs.size - fixedPrefixSize

/--
  Given a predefinition with value `fun (x_₁ ... xₙ) (y_₁ : α₁)... (yₘ : αₘ) => ...`,
  where `n = fixedPrefixSize`, return an array `A` s.t. `i ∈ A` iff `sizeOf yᵢ` reduces to a literal.
  This is the case for types such as `Prop`, `Type u`, etc.
  This arguments should not be considered when guessing a well-founded relation.
  See `generateCombinations?`
-/
def getForbiddenByTrivialSizeOf (fixedPrefixSize : Nat) (preDef : PreDefinition) : MetaM (Array Nat) :=
  lambdaTelescope preDef.value fun xs _ => do
    let mut result := #[]
    for x in xs[fixedPrefixSize:], i in [:xs.size] do
      try
        let sizeOf ← whnfD (← mkAppM ``sizeOf #[x])
        if sizeOf.isLit then
         result := result.push i
      catch _ =>
        result := result.push i
    return result

def generateCombinations? (forbiddenArgs : Array (Array Nat)) (numArgs : Array Nat) (threshold : Nat := 32) : Option (Array (Array Nat)) :=
  go 0 #[] |>.run #[] |>.2
where
  isForbidden (fidx : Nat) (argIdx : Nat) : Bool :=
    if h : fidx < forbiddenArgs.size then
       forbiddenArgs.get ⟨fidx, h⟩ |>.contains argIdx
    else
      false

  go (fidx : Nat) : OptionT (ReaderT (Array Nat) (StateM (Array (Array Nat)))) Unit := do
    if h : fidx < numArgs.size then
      let n := numArgs.get ⟨fidx, h⟩
      for argIdx in [:n] do
        unless isForbidden fidx argIdx do
          withReader (·.push argIdx) (go (fidx + 1))
    else
      modify (·.push (← read))
      if (← get).size > threshold then
        failure
termination_by _ fidx => numArgs.size - fidx

def elabWFRel (preDefs : Array PreDefinition) (unaryPreDefName : Name) (fixedPrefixSize : Nat) (argType : Expr) (wf? : Option TerminationWF) (k : Expr → TermElabM α) : TermElabM α := do
  let α := argType
  let u ← getLevel α
  let expectedType := mkApp (mkConst ``WellFoundedRelation [u]) α
  trace[Elab.definition.wf] "elabWFRel start: {(← mkFreshTypeMVar).mvarId!}"
  match wf? with
  | some (TerminationWF.core wfStx) => withDeclName unaryPreDefName do
      let wfRel ← instantiateMVars (← withSynthesize <| elabTermEnsuringType wfStx expectedType)
      let pendingMVarIds ← getMVars wfRel
      discard <| logUnassignedUsingErrorInfos pendingMVarIds
      k wfRel
  | some (TerminationWF.ext elements) => go expectedType elements
  | none => guess expectedType
where
  go (expectedType : Expr) (elements : Array TerminationByElement) : TermElabM α :=
    withDeclName unaryPreDefName <| withRef (getRefFromElems elements) do
      let mainMVarId := (← mkFreshExprSyntheticOpaqueMVar expectedType).mvarId!
      let [fMVarId, wfRelMVarId, _] ← mainMVarId.apply (← mkConstWithFreshMVarLevels ``invImage) | throwError "failed to apply 'invImage'"
      let (d, fMVarId) ← fMVarId.intro1
      let subgoals ← unpackMutual preDefs fMVarId d
      for (d, mvarId) in subgoals, element in elements, preDef in preDefs do
        let mvarId ← unpackUnary preDef fixedPrefixSize mvarId d element
        mvarId.withContext do
          let value ← Term.withSynthesize <| elabTermEnsuringType element.body (← mvarId.getType)
          mvarId.assign value
      let wfRelVal ← synthInstance (← inferType (mkMVar wfRelMVarId))
      wfRelMVarId.assign wfRelVal
      k (← instantiateMVars (mkMVar mainMVarId))

  generateElements (numArgs : Array Nat) (argCombination : Array Nat) : TermElabM (Array TerminationByElement) := do
    let mut result := #[]
    let var ← `(x)
    let hole ← `(_)
    for preDef in preDefs, numArg in numArgs, argIdx in argCombination, i in [:preDefs.size] do
      let mut vars := #[var]
      for _ in [:numArg - argIdx - 1] do
        vars := vars.push hole
      -- TODO: improve this.
      -- The following trick allows a function `f` in a mutual block to invoke `g` appearing before it with the input argument.
      -- We should compute the "right" order (if there is one) in the future.
      let body ← if preDefs.size > 1 then `((sizeOf x, $(quote i))) else `(sizeOf x)
      result := result.push {
        ref := preDef.ref
        declName := preDef.declName
        vars := vars
        body := body
        implicit := false
      }
    return result

  guess (expectedType : Expr) : TermElabM α := do
    -- TODO: add support for lex
    let numArgs ← getNumCandidateArgs fixedPrefixSize preDefs
    -- TODO: include in `forbiddenArgs` arguments that are fixed but are not in the fixed prefix
    let forbiddenArgs ← preDefs.mapM fun preDef => getForbiddenByTrivialSizeOf fixedPrefixSize preDef
    -- TODO: add option to control the maximum number of cases to try
    if let some combs := generateCombinations? forbiddenArgs numArgs then
      for comb in combs do
        let elements ← generateElements numArgs comb
        if let some r ← observing? (go expectedType elements) then
          return r
    throwError "failed to prove termination, use `termination_by` to specify a well-founded relation"

end Lean.Elab.WF
