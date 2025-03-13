/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.TerminationMeasure
import Lean.Elab.PreDefinition.Mutual
import Lean.Elab.PreDefinition.WF.PackMutual
import Lean.Elab.PreDefinition.WF.FloatRecApp
import Lean.Elab.PreDefinition.WF.Rel
import Lean.Elab.PreDefinition.WF.Fix
import Lean.Elab.PreDefinition.WF.Unfold
import Lean.Elab.PreDefinition.WF.Preprocess
import Lean.Elab.PreDefinition.WF.GuessLex

namespace Lean.Elab
open WF
open Meta

def wfRecursion (preDefs : Array PreDefinition) (termMeasure?s : Array (Option TerminationMeasure)) : TermElabM Unit := do
  let termMeasures? := termMeasure?s.mapM id -- Either all or none, checked by `elabTerminationByHints`
  let preDefs ← preDefs.mapM fun preDef =>
    return { preDef with value := (← floatRecApp preDef.value) }
  let (fixedParamPerms, argsPacker, unaryPreDef, wfPreprocessProofs) ← withoutModifyingEnv do
    for preDef in preDefs do
      addAsAxiom preDef
    let fixedParamPerms ← getFixedParamPerms preDefs
    let varNamess ← preDefs.mapIdxM fun i preDef => varyingVarNames fixedParamPerms i preDef
    for varNames in varNamess, preDef in preDefs do
      if varNames.isEmpty then
        throwError "well-founded recursion cannot be used, '{preDef.declName}' does not take any (non-fixed) arguments"
    let argsPacker := { varNamess }
    let (preDefsAttached, wfPreprocessProofs) ← Array.unzip <$> preDefs.mapM fun preDef => do
      let result ← preprocess preDef.value
      return ({preDef with value := result.expr}, result)
    let unaryPreDef ← packMutual fixedParamPerms argsPacker preDefsAttached
    return (fixedParamPerms, argsPacker, unaryPreDef, wfPreprocessProofs)
  trace[Elab.definition.wf] "unaryPreDef:{indentD unaryPreDef.value}"

  let wf : TerminationMeasures ← do
    if let some tms := termMeasures? then pure tms else
    -- No termination_by here, so use GuessLex to infer one
    guessLex preDefs unaryPreDef fixedParamPerms argsPacker

  let preDefNonRec ← forallBoundedTelescope unaryPreDef.type fixedParamPerms.numFixed fun fixedArgs type => do
    let type ← whnfForall type
    unless type.isForall do
      throwError "wfRecursion: expected unary function type: {type}"
    let packedArgType := type.bindingDomain!
    elabWFRel (preDefs.map (·.declName)) unaryPreDef.declName fixedParamPerms fixedArgs argsPacker packedArgType wf fun wfRel => do
      trace[Elab.definition.wf] "wfRel: {wfRel}"
      let (value, envNew) ← withoutModifyingEnv' do
        addAsAxiom unaryPreDef
        let value ← mkFix unaryPreDef fixedArgs argsPacker wfRel (preDefs.map (·.declName)) (preDefs.map (·.termination.decreasingBy?))
        eraseRecAppSyntaxExpr value
      /- `mkFix` invokes `decreasing_tactic` which may add auxiliary theorems to the environment. -/
      let value ← unfoldDeclsFrom envNew value
      return { unaryPreDef with value }

  trace[Elab.definition.wf] ">> {preDefNonRec.declName} :=\n{preDefNonRec.value}"
  let preDefsNonrec ← preDefsFromUnaryNonRec fixedParamPerms argsPacker preDefs preDefNonRec
  Mutual.addPreDefsFromUnary preDefs preDefsNonrec preDefNonRec
  let preDefs ← Mutual.cleanPreDefs preDefs
  registerEqnsInfo preDefs preDefNonRec.declName fixedParamPerms argsPacker
  for preDef in preDefs, wfPreprocessProof in wfPreprocessProofs do
    unless preDef.kind.isTheorem do
      unless (← isProp preDef.type) do
        WF.mkUnfoldEq preDef preDefNonRec.declName wfPreprocessProof
  -- must happen before `addPreDefAttributes` enables realizations for the top-level functions,
  -- which may need to use realizations on `preDefNonRec`
  enableRealizationsForConst preDefNonRec.declName
  Mutual.addPreDefAttributes preDefs

builtin_initialize registerTraceClass `Elab.definition.wf

end Lean.Elab
