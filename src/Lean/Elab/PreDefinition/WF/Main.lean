/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.TerminationArgument
import Lean.Elab.PreDefinition.WF.PackMutual
import Lean.Elab.PreDefinition.WF.Preprocess
import Lean.Elab.PreDefinition.WF.Rel
import Lean.Elab.PreDefinition.WF.Fix
import Lean.Elab.PreDefinition.WF.Eqns
import Lean.Elab.PreDefinition.WF.Ite
import Lean.Elab.PreDefinition.WF.GuessLex

namespace Lean.Elab
open WF
open Meta

def wfRecursion (preDefs : Array PreDefinition) (termArg?s : Array (Option TerminationArgument)) : TermElabM Unit := do
  let termArgs? := termArg?s.mapM id -- Either all or none, checked by `elabTerminationByHints`
  let preDefs ← preDefs.mapM fun preDef =>
    return { preDef with value := (← preprocess preDef.value) }
  let (fixedPrefixSize, argsPacker, unaryPreDef) ← withoutModifyingEnv do
    for preDef in preDefs do
      addAsAxiom preDef
    let fixedPrefixSize ← getFixedPrefix preDefs
    trace[Elab.definition.wf] "fixed prefix: {fixedPrefixSize}"
    let varNamess ← preDefs.mapM (varyingVarNames fixedPrefixSize ·)
    for varNames in varNamess, preDef in preDefs do
      if varNames.isEmpty then
        throwError "well-founded recursion cannot be used, '{preDef.declName}' does not take any (non-fixed) arguments"
    let argsPacker := { varNamess }
    let preDefsDIte ← preDefs.mapM fun preDef => return { preDef with value := (← iteToDIte preDef.value) }
    return (fixedPrefixSize, argsPacker, ← packMutual fixedPrefixSize argsPacker preDefsDIte)

  let wf : TerminationArguments ← do
    if let some tas := termArgs? then pure tas else
    -- No termination_by here, so use GuessLex to infer one
    guessLex preDefs unaryPreDef fixedPrefixSize argsPacker

  let preDefNonRec ← forallBoundedTelescope unaryPreDef.type fixedPrefixSize fun prefixArgs type => do
    let type ← whnfForall type
    unless type.isForall do
      throwError "wfRecursion: expected unary function type: {type}"
    let packedArgType := type.bindingDomain!
    elabWFRel (preDefs.map (·.declName)) unaryPreDef.declName prefixArgs argsPacker packedArgType wf fun wfRel => do
      trace[Elab.definition.wf] "wfRel: {wfRel}"
      let (value, envNew) ← withoutModifyingEnv' do
        addAsAxiom unaryPreDef
        let value ← mkFix unaryPreDef prefixArgs argsPacker wfRel (preDefs.map (·.termination.decreasingBy?))
        eraseRecAppSyntaxExpr value
      /- `mkFix` invokes `decreasing_tactic` which may add auxiliary theorems to the environment. -/
      let value ← unfoldDeclsFrom envNew value
      return { unaryPreDef with value }

  trace[Elab.definition.wf] ">> {preDefNonRec.declName} :=\n{preDefNonRec.value}"
  addPreDefsFromUnary preDefs fixedPrefixSize argsPacker preDefNonRec (hasInduct := true)

builtin_initialize registerTraceClass `Elab.definition.wf

end Lean.Elab
