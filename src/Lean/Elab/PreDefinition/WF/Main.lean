/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.WF.TerminationHint
import Lean.Elab.PreDefinition.WF.PackDomain
import Lean.Elab.PreDefinition.WF.PackMutual
import Lean.Elab.PreDefinition.WF.Rel
import Lean.Elab.PreDefinition.WF.Fix
import Lean.Elab.PreDefinition.WF.Eqns
import Lean.Elab.PreDefinition.WF.Ite

namespace Lean.Elab
open WF
open Meta

private partial def addNonRecPreDefs (preDefs : Array PreDefinition) (preDefNonRec : PreDefinition) (fixedPrefixSize : Nat) : TermElabM Unit := do
  let us := preDefNonRec.levelParams.map mkLevelParam
  let all := preDefs.toList.map (·.declName)
  for fidx in [:preDefs.size] do
    let preDef := preDefs[fidx]!
    let value ← lambdaTelescope preDef.value fun xs _ => do
      let packedArgs : Array Expr := xs[fixedPrefixSize:]
      let mkProd (type : Expr) : MetaM Expr := do
        mkUnaryArg type packedArgs
      let rec mkSum (i : Nat) (type : Expr) : MetaM Expr := do
        if i == preDefs.size - 1 then
          mkProd type
        else
          (← whnfD type).withApp fun f args => do
            assert! args.size == 2
            if i == fidx then
              return mkApp3 (mkConst ``PSum.inl f.constLevels!) args[0]! args[1]! (← mkProd args[0]!)
            else
              let r ← mkSum (i+1) args[1]!
              return mkApp3 (mkConst ``PSum.inr f.constLevels!) args[0]! args[1]! r
      let Expr.forallE _ domain _ _ := (← instantiateForall preDefNonRec.type xs[:fixedPrefixSize]) | unreachable!
      let arg ← mkSum 0 domain
      mkLambdaFVars xs (mkApp (mkAppN (mkConst preDefNonRec.declName us) xs[:fixedPrefixSize]) arg)
    trace[Elab.definition.wf] "{preDef.declName} := {value}"
    addNonRec { preDef with value } (applyAttrAfterCompilation := false) (all := all)

partial def withCommonTelescope (preDefs : Array PreDefinition) (k : Array Expr → Array Expr → TermElabM α) : TermElabM α :=
  go #[] (preDefs.map (·.value))
where
  go (fvars : Array Expr) (vals : Array Expr) : TermElabM α := do
    if !(vals.all fun val => val.isLambda) then
      k fvars vals
    else if !(← vals.allM fun val => return val.bindingName! == vals[0]!.bindingName! && val.binderInfo == vals[0]!.binderInfo && (← isDefEq val.bindingDomain! vals[0]!.bindingDomain!)) then
      k fvars vals
    else
      withLocalDecl vals[0]!.bindingName! vals[0]!.binderInfo vals[0]!.bindingDomain! fun x =>
        go (fvars.push x) (vals.map fun val => val.bindingBody!.instantiate1 x)

def getFixedPrefix (preDefs : Array PreDefinition) : TermElabM Nat :=
  withCommonTelescope preDefs fun xs vals => do
    let resultRef ← IO.mkRef xs.size
    for val in vals do
      if (← resultRef.get) == 0 then return 0
      forEachExpr' val fun e => do
        if preDefs.any fun preDef => e.isAppOf preDef.declName then
          let args := e.getAppArgs
          resultRef.modify (min args.size ·)
          for arg in args, x in xs do
            if !(← withoutProofIrrelevance <| withReducible <| isDefEq arg x) then
              -- We continue searching if e's arguments are not a prefix of `xs`
              return true
          return false
        else
          return true
    resultRef.get

private def isOnlyOneUnaryDef (preDefs : Array PreDefinition) (fixedPrefixSize : Nat) : MetaM Bool := do
  if preDefs.size == 1 then
    lambdaTelescope preDefs[0]!.value fun xs _ => return xs.size == fixedPrefixSize + 1
  else
    return false

def wfRecursion (preDefs : Array PreDefinition) (wf? : Option TerminationWF) (decrTactic? : Option Syntax) : TermElabM Unit := do
  let (unaryPreDef, fixedPrefixSize) ← withoutModifyingEnv do
    for preDef in preDefs do
      addAsAxiom preDef
    let fixedPrefixSize ← getFixedPrefix preDefs
    trace[Elab.definition.wf] "fixed prefix: {fixedPrefixSize}"
    let preDefsDIte ← preDefs.mapM fun preDef => return { preDef with value := (← iteToDIte preDef.value) }
    let unaryPreDefs ← packDomain fixedPrefixSize preDefsDIte
    return (← packMutual fixedPrefixSize preDefs unaryPreDefs, fixedPrefixSize)
  let preDefNonRec ← forallBoundedTelescope unaryPreDef.type fixedPrefixSize fun prefixArgs type => do
    let type ← whnfForall type
    let packedArgType := type.bindingDomain!
    elabWFRel preDefs unaryPreDef.declName fixedPrefixSize packedArgType wf? fun wfRel => do
      trace[Elab.definition.wf] "wfRel: {wfRel}"
      let (value, envNew) ← withoutModifyingEnv' do
        addAsAxiom unaryPreDef
        let value ← mkFix unaryPreDef prefixArgs wfRel decrTactic?
        eraseRecAppSyntaxExpr value
      /- `mkFix` invokes `decreasing_tactic` which may add auxiliary theorems to the environment. -/
      let value ← unfoldDeclsFrom envNew value
      return { unaryPreDef with value }
  trace[Elab.definition.wf] ">> {preDefNonRec.declName} :=\n{preDefNonRec.value}"
  let preDefs ← preDefs.mapM fun d => eraseRecAppSyntax d
  if (← isOnlyOneUnaryDef preDefs fixedPrefixSize) then
    addNonRec preDefNonRec (applyAttrAfterCompilation := false)
  else
    withEnableInfoTree false do
      addNonRec preDefNonRec (applyAttrAfterCompilation := false)
    addNonRecPreDefs preDefs preDefNonRec fixedPrefixSize
  -- We create the `_unsafe_rec` before we abstract nested proofs.
  -- Reason: the nested proofs may be referring to the _unsafe_rec.
  addAndCompilePartialRec preDefs
  let preDefs ← preDefs.mapM (abstractNestedProofs ·)
  registerEqnsInfo preDefs preDefNonRec.declName fixedPrefixSize
  for preDef in preDefs do
    applyAttributesOf #[preDef] AttributeApplicationTime.afterCompilation

builtin_initialize registerTraceClass `Elab.definition.wf

end Lean.Elab
