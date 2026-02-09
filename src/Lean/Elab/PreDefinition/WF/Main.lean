/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Elab.PreDefinition.WF.PackMutual
public import Lean.Elab.PreDefinition.WF.FloatRecApp
public import Lean.Elab.PreDefinition.WF.Rel
public import Lean.Elab.PreDefinition.WF.Fix
public import Lean.Elab.PreDefinition.WF.Unfold
public import Lean.Elab.PreDefinition.WF.Preprocess
public import Lean.Elab.PreDefinition.WF.GuessLex

public section

namespace Lean.Elab
open WF
open Meta

def wfRecursion (docCtx : LocalContext × LocalInstances) (preDefs : Array PreDefinition) (termMeasure?s : Array (Option TerminationMeasure)) : TermElabM Unit := do
  let termMeasures? := termMeasure?s.mapM id -- Either all or none, checked by `elabTerminationByHints`
  let preDefs ← preDefs.mapM fun preDef =>
    return { preDef with value := (← floatRecApp preDef.value) }
  let (fixedParamPerms, argsPacker, unaryPreDef) ← withoutModifyingEnv do
    for preDef in preDefs do
      addAsAxiom preDef
    let fixedParamPerms ← getFixedParamPerms preDefs
    let varNamess ← preDefs.mapIdxM fun i preDef => varyingVarNames fixedParamPerms i preDef
    for varNames in varNamess, preDef in preDefs do
      if varNames.isEmpty then
        throwError "well-founded recursion cannot be used, `{preDef.declName}` does not take any (non-fixed) arguments"
    let argsPacker := { varNamess }
    let numSectionVars := preDefs[0]!.numSectionVars
    let preDefs' ← preDefs.mapM fun preDef => do
      return { preDef with value := (← unfoldIfArgIsAppOf (preDefs.map (·.declName)) numSectionVars preDef.value) }
    let unaryPreDef ← packMutual fixedParamPerms argsPacker preDefs'
    return (fixedParamPerms, argsPacker, unaryPreDef)
  trace[Elab.definition.wf] "unaryPreDef:{indentD unaryPreDef.value}"

  let (unaryPreDefProcessed, wfPreprocessProof) ← withoutModifyingEnv do
    addAsAxiom unaryPreDef
    let result ← preprocess unaryPreDef.value
    pure ({unaryPreDef with value := result.expr}, result)
  trace[Elab.definition.wf] "unaryPreDefProcessed:{indentD unaryPreDef.value}"

  let wf : TerminationMeasures ← do
    if let some tms := termMeasures? then pure tms else
    withoutExporting do  -- generating proof
    -- No termination_by here, so use GuessLex to infer one
    guessLex preDefs unaryPreDefProcessed fixedParamPerms argsPacker

  let preDefNonRec ← forallBoundedTelescope unaryPreDef.type fixedParamPerms.numFixed fun fixedArgs type => do
    let type ← whnfForall type
    unless type.isForall do
      throwError "wfRecursion: expected unary function type: {type}"
    let packedArgType := type.bindingDomain!
    elabWFRel (preDefs.map (·.declName)) unaryPreDef.declName fixedParamPerms fixedArgs argsPacker packedArgType wf fun wfRel => do
      trace[Elab.definition.wf] "wfRel: {wfRel}"
      let useNatRec := (← isNatLtWF wfRel).isSome
      -- Warn about likely unwanted reducibility attributes
      unless useNatRec do
        preDefs.forM fun preDef =>
          preDef.modifiers.attrs.forM fun a => do
            if a.name = `reducible || a.name = `semireducible then
              logWarningAt a.stx s!"marking functions defined by well-founded recursion as `{a.name}` is not effective"

      let (value, envNew) ← withoutModifyingEnv' do
        addAsAxiom unaryPreDef
        let value ← mkFix unaryPreDefProcessed fixedArgs argsPacker wfRel (preDefs.map (·.declName)) (preDefs.map (·.termination.decreasingBy?))
        eraseRecAppSyntaxExpr value
      /- `mkFix` invokes `decreasing_tactic` which may add auxiliary theorems to the environment. -/
      let value ← unfoldDeclsFrom envNew value
      -- Make sure we remember invoked tactics
      modifyEnv (copyExtraModUses envNew)
      return { unaryPreDefProcessed with value }

  trace[Elab.definition.wf] ">> {preDefNonRec.declName} :=\n{preDefNonRec.value}"
  let preDefsNonrec ← preDefsFromUnaryNonRec fixedParamPerms argsPacker preDefs preDefNonRec
  Mutual.addPreDefsFromUnary (cacheProofs := false) docCtx preDefs preDefsNonrec preDefNonRec
  addAndCompilePartialRec docCtx preDefs
  let unaryPreDef ← Mutual.cleanPreDef (cacheProofs := false) unaryPreDef
  let preDefs ← preDefs.mapM (Mutual.cleanPreDef (cacheProofs := false) ·)
  registerEqnsInfo preDefs preDefNonRec.declName fixedParamPerms argsPacker
  markAsRecursive unaryPreDef.declName
  unless (← isProp unaryPreDef.type) do
    WF.mkUnfoldEq unaryPreDef preDefNonRec.declName wfPreprocessProof
  for preDef in preDefs do
    unless preDef.declName = preDefNonRec.declName do
      unless preDef.kind.isTheorem do
        unless (← isProp preDef.type) do
          WF.mkBinaryUnfoldEq preDef preDefNonRec.declName
  -- must happen before `addPreDefAttributes` enables realizations for the top-level functions,
  -- which may need to use realizations on `preDefNonRec`
  enableRealizationsForConst preDefNonRec.declName
  Mutual.addPreDefAttributes preDefs

builtin_initialize registerTraceClass `Elab.definition.wf

end Lean.Elab
