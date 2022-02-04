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
              return mkApp3 (mkConst ``Sum.inl f.constLevels!) args[0] args[1] (← mkProd args[0])
            else
              let r ← mkSum (i+1) args[1]
              return mkApp3 (mkConst ``Sum.inr f.constLevels!) args[0] args[1] r
      let arg ← mkSum 0 domain
      mkLambdaFVars xs (mkApp (mkConst preDefNonRec.declName us) arg)
    trace[Elab.definition.wf] "{preDef.declName} := {value}"
    addNonRec { preDef with value } (applyAttrAfterCompilation := false)

def wfRecursion (preDefs : Array PreDefinition) (wf? : Option TerminationWF) (decrTactic? : Option Syntax) : TermElabM Unit := do
  let unaryPreDef ← withoutModifyingEnv do
    for preDef in preDefs do
      addAsAxiom preDef
    let unaryPreDefs ← packDomain preDefs
    packMutual unaryPreDefs
  let wfRel ← elabWFRel preDefs unaryPreDef wf?
  let preDefNonRec ← withoutModifyingEnv do
    addAsAxiom unaryPreDef
    mkFix unaryPreDef wfRel decrTactic?
  let preDefNonRec ← eraseRecAppSyntax preDefNonRec
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
