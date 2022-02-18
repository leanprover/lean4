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

namespace Lean.Elab
open WF
open Meta

private def isOnlyOneUnaryDef (preDefs : Array PreDefinition) : MetaM Bool := do
  if preDefs.size == 1 then
    lambdaTelescope preDefs[0].value fun xs _ => return xs.size == 1
  else
    return false

private partial def addNonRecPreDefs (preDefs : Array PreDefinition) (preDefNonRec : PreDefinition) : TermElabM Unit := do
  if (← isOnlyOneUnaryDef preDefs) then
    return ()
  let Expr.forallE _ domain _ _ := preDefNonRec.type | unreachable!
  let us := preDefNonRec.levelParams.map mkLevelParam
  for fidx in [:preDefs.size] do
    let preDef := preDefs[fidx]
    let value ← lambdaTelescope preDef.value fun xs _ => do
      let mkProd (type : Expr) : MetaM Expr := do
        mkUnaryArg type xs
      let rec mkSum (i : Nat) (type : Expr) : MetaM Expr := do
        if i == preDefs.size - 1 then
          mkProd type
        else
          (← whnfD type).withApp fun f args => do
            assert! args.size == 2
            if i == fidx then
              return mkApp3 (mkConst ``PSum.inl f.constLevels!) args[0] args[1] (← mkProd args[0])
            else
              let r ← mkSum (i+1) args[1]
              return mkApp3 (mkConst ``PSum.inr f.constLevels!) args[0] args[1] r
      let arg ← mkSum 0 domain
      mkLambdaFVars xs (mkApp (mkConst preDefNonRec.declName us) arg)
    trace[Elab.definition.wf] "{preDef.declName} := {value}"
    addNonRec { preDef with value } (applyAttrAfterCompilation := false)

partial def withCommonTelescope (preDefs : Array PreDefinition) (k : Array Expr → Array Expr → TermElabM α) : TermElabM α :=
  go #[] (preDefs.map (·.value))
where
  go (fvars : Array Expr) (vals : Array Expr) : TermElabM α := do
    if !(vals.all fun val => val.isLambda) then
      k fvars vals
    else if !(← vals.allM fun val => return val.bindingName! == vals[0].bindingName! && val.binderInfo == vals[0].binderInfo && (← isDefEq val.bindingDomain! vals[0].bindingDomain!)) then
      k fvars vals
    else
      withLocalDecl vals[0].bindingName! vals[0].binderInfo vals[0].bindingDomain! fun x =>
        go (fvars.push x) (vals.map fun val => val.bindingBody!.instantiate1 x)

def getFixedPrefix (preDefs : Array PreDefinition) : TermElabM Nat :=
  withCommonTelescope preDefs fun xs vals => do
    let resultRef ← IO.mkRef xs.size
    for val in vals do
      if (← resultRef.get) == 0 then return 0
      forEachExpr' val fun e => do
        if preDefs.any fun preDef => e.isAppOf preDef.declName then
          let args := e.getAppArgs
          resultRef.modify (min args.size .)
          for arg in args, x in xs do
            if !(← withoutProofIrrelevance <| withReducible <| isDefEq arg x) then
              -- We continue searching if e's arguments are not a prefix of `xs`
              return true
          return false
        else
          return true
    resultRef.get

def wfRecursion (preDefs : Array PreDefinition) (wf? : Option TerminationWF) (decrTactic? : Option Syntax) : TermElabM Unit := do
  let fixedPrefixSize ← getFixedPrefix preDefs
  trace[Elab.definition.wf] "fixed prefix: {fixedPrefixSize}"
  let fixedPrefixSize := 0 -- TODO: remove after we convert all code in this module to use the fixedPrefix
  let unaryPreDef ← withoutModifyingEnv do
    for preDef in preDefs do
      addAsAxiom preDef
    let unaryPreDefs ← packDomain fixedPrefixSize preDefs
    -- unaryPreDefs.forM fun d => do trace[Elab.definition.wf] "packDomain result {d.declName} := {d.value}"; check d.value
    packMutual fixedPrefixSize unaryPreDefs
  -- trace[Elab.definition.wf] "after packMutual {unaryPreDef.declName} := {unaryPreDef.value}"
  let preDefNonRec ← forallBoundedTelescope unaryPreDef.type fixedPrefixSize fun prefixArgs type => do
    let packedArgType := type.bindingDomain!
    let wfRel ← elabWFRel preDefs unaryPreDef.declName fixedPrefixSize packedArgType wf?
    trace[Elab.definition.wf] "wfRel: {wfRel}"
    withoutModifyingEnv do
      addAsAxiom unaryPreDef
      let value ← mkFix unaryPreDef prefixArgs wfRel decrTactic?
      let value ← eraseRecAppSyntaxExpr value
      return { unaryPreDef with value }
  trace[Elab.definition.wf] ">> {preDefNonRec.declName} :=\n{preDefNonRec.value}"
  let preDefs ← preDefs.mapM fun d => eraseRecAppSyntax d
  addNonRec preDefNonRec
  addNonRecPreDefs preDefs preDefNonRec
  registerEqnsInfo preDefs preDefNonRec.declName
  for preDef in preDefs do
    applyAttributesOf #[preDef] AttributeApplicationTime.afterCompilation
  addAndCompilePartialRec preDefs

builtin_initialize registerTraceClass `Elab.definition.wf

end Lean.Elab
