/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Joachim Breitner
-/
prelude
import Lean.Elab.PreDefinition.TerminationMeasure
import Lean.Elab.PreDefinition.Mutual
import Lean.Elab.PreDefinition.Structural.Basic
import Lean.Elab.PreDefinition.Structural.FindRecArg
import Lean.Elab.PreDefinition.Structural.Preprocess
import Lean.Elab.PreDefinition.Structural.BRecOn
import Lean.Elab.PreDefinition.Structural.IndPred
import Lean.Elab.PreDefinition.Structural.Eqns
import Lean.Elab.PreDefinition.Structural.SmartUnfolding
import Lean.Meta.Tactic.TryThis

namespace Lean.Elab
namespace Structural
open Meta

private def getFixedPrefix (declName : Name) (xs : Array Expr) (value : Expr) : MetaM Nat := do
  let numFixedRef ← IO.mkRef xs.size
  forEachExpr' value fun e => do
    if e.isAppOf declName then
      let args := e.getAppArgs
      numFixedRef.modify fun numFixed => if args.size < numFixed then args.size else numFixed
      for arg in args, x in xs do
        /- We should not use structural equality here. For example, given the definition
           ```
           def V.map {α β} f x x_1 :=
             @V.map.match_1.{1} α (fun x x_2 => V β x) x x_1
               (fun x x_2 => @V.mk₁ β x (f Bool.true x_2))
               (fun e => @V.mk₂ β (V.map (fun b => α b) (fun b => β b) f Bool.false e))
           ```
           The first three arguments at `V.map (fun b => α b) (fun b => β b) f Bool.false e` are "fixed"
           modulo definitional equality.

           We disable to proof irrelevance to be able to use structural recursion on inductive predicates.
           For example, consider the example
           ```
           inductive PList (α : Type) : Prop
           | nil
           | cons : α → PList α → PList α

           infixr:67 " ::: " => PList.cons

           set_option trace.Elab.definition.structural true in
           def pmap {α β} (f : α → β) : PList α → PList β
             | PList.nil => PList.nil
             | a:::as => f a ::: pmap f as
           ```
          The "Fixed" prefix would be 4 since all elements of type `PList α` are definitionally equal.
        -/
        if !(← withoutProofIrrelevance <| withReducible <| isDefEq arg x) then
          -- We continue searching if e's arguments are not a prefix of `xs`
          return true
      return false
    else
      return true
  numFixedRef.get

partial def withCommonTelescope (preDefs : Array PreDefinition) (k : Array Expr → Array Expr → M α) : M α :=
  go #[] (preDefs.map (·.value))
where
  go (fvars : Array Expr) (vals : Array Expr) : M α := do
    if !(vals.all fun val => val.isLambda) then
      k fvars vals
    else if !(← vals.allM fun val=> isDefEq val.bindingDomain! vals[0]!.bindingDomain!) then
      k fvars vals
    else
      withLocalDecl vals[0]!.bindingName! vals[0]!.binderInfo vals[0]!.bindingDomain! fun x =>
        go (fvars.push x) (vals.map fun val => val.bindingBody!.instantiate1 x)

private def elimMutualRecursion (preDefs : Array PreDefinition) (fixedParamPerms : FixedParamPerms)
    (xs : Array Expr) (recArgInfos : Array RecArgInfo) : M (Array PreDefinition) := do
  let values ← preDefs.mapIdxM (fixedParamPerms.perms[·]!.instantiateLambda ·.value xs)
  let indInfo ← getConstInfoInduct recArgInfos[0]!.indGroupInst.all[0]!
  if ← isInductivePredicate indInfo.name then
    -- Here we branch off to the IndPred construction, but only for non-mutual functions
    unless preDefs.size = 1 do
      throwError "structural mutual recursion over inductive predicates is not supported"
    trace[Elab.definition.structural] "Using mkIndPred construction"
    let preDef := preDefs[0]!
    let recArgInfo := recArgInfos[0]!
    let value := values[0]!
    let valueNew ← mkIndPredBRecOn recArgInfo value
    let valueNew ← lambdaTelescope value fun ys _ => do
      mkLambdaFVars (etaReduce := true) (fixedParamPerms.perms[0]!.buildArgs xs ys) (mkAppN valueNew ys)
    trace[Elab.definition.structural] "Nonrecursive value:{indentExpr valueNew}"
    check valueNew
    return #[{ preDef with value := valueNew }]

  -- Groups the (indices of the) definitions by their position in indInfo.all
  let positions : Positions := .groupAndSort (·.indIdx) recArgInfos (Array.range indInfo.numTypeFormers)
  trace[Elab.definition.structural] "assignments of type formers of {indInfo.name} to functions: {positions}"

  -- Construct the common `.brecOn` arguments
  let motives ← (Array.zip recArgInfos values).mapM fun (r, v) => mkBRecOnMotive r v
  trace[Elab.definition.structural] "motives: {motives}"
  let brecOnConst ← mkBRecOnConst recArgInfos positions motives
  let FTypes ← inferBRecOnFTypes recArgInfos positions brecOnConst
  trace[Elab.definition.structural] "FTypes: {FTypes}"
  let FArgs ← (recArgInfos.zip (values.zip FTypes)).mapM fun (r, (v, t)) =>
    mkBRecOnF recArgInfos positions r v t
  trace[Elab.definition.structural] "FArgs: {FArgs}"
  -- Assemble the individual `.brecOn` applications
  let valuesNew ← (Array.zip recArgInfos values).mapIdxM fun i (r, v) =>
    mkBrecOnApp positions i brecOnConst FArgs r v
  -- Abstract over the fixed prefixed, preserving the original parameter order
  let valuesNew ← (values.zip valuesNew).mapIdxM fun i ⟨value, valueNew⟩ =>
    lambdaTelescope value fun ys _ => do
      -- NB: Do not eta-contract here, other code (e.g. FunInd) expects this to have the
      -- same number of head lambdas as the original definition
      mkLambdaFVars (fixedParamPerms.perms[i]!.buildArgs xs ys) (valueNew.beta ys)
  return (Array.zip preDefs valuesNew).map fun ⟨preDef, valueNew⟩ => { preDef with value := valueNew }

private def inferRecArgPos (preDefs : Array PreDefinition) (termMeasure?s : Array (Option TerminationMeasure)) :
    M (Array Nat × (Array PreDefinition) × FixedParamPerms) := do
  withoutModifyingEnv do
    preDefs.forM (addAsAxiom ·)
    let fnNames := preDefs.map (·.declName)
    let preDefs ← preDefs.mapM fun preDef =>
      return { preDef with value := (← preprocess preDef.value fnNames) }

    -- The syntactically fixed arguments
    let fixedParamPerms ← getFixedParamPerms preDefs

    fixedParamPerms.perms[0]!.forallTelescope preDefs[0]!.type fun xs => do
      let values ← preDefs.mapIdxM (fixedParamPerms.perms[·]!.instantiateLambda ·.value xs)

      tryAllArgs fnNames fixedParamPerms xs values termMeasure?s fun recArgInfos => do
        let recArgPoss := recArgInfos.map (·.recArgPos)
        trace[Elab.definition.structural] "Trying argument set {recArgPoss}"
        let (fixedParamPerms', xs', toErase) := fixedParamPerms.erase xs (recArgInfos.map (·.indicesAndRecArgPos))
        -- We may have to turn some fixed parameters into varying parameters
        let recArgInfos := recArgInfos.mapIdx fun i recArgInfo =>
          {recArgInfo with fixedParamPerm := fixedParamPerms'.perms[i]!}
        if xs'.size != xs.size then
          trace[Elab.definition.structural] "Reduced fixed params from {xs} to {xs'}, erasing {toErase.map mkFVar}"
          trace[Elab.definition.structural] "New recArgInfos {repr recArgInfos}"
        -- Check that the parameters of the IndGroupInsts are still fine
          for recArgInfo in recArgInfos do
            for indParam in recArgInfo.indGroupInst.params do
              for y in toErase do
                if (← dependsOn indParam y) then
                  if indParam.isFVarOf y then
                    throwError "its type is an inductive datatype and the datatype parameter\
                      {indentExpr indParam}\n\
                      which cannot be fixed as it is an index or depends on an index, and indices \
                      cannot be fixed parameters when using structural recursion."
                  else
                    throwError "its type is an inductive datatype and the datatype parameter\
                      {indentExpr indParam}\ndepends on the function parameter{indentExpr (mkFVar y)}\n\
                      which cannot be fixed as it is an index or depends on an index, and indices \
                      cannot be fixed parameters when using structural recursion."
        withErasedFVars toErase do
          let preDefs' ← elimMutualRecursion preDefs fixedParamPerms' xs' recArgInfos
          return (recArgPoss, preDefs', fixedParamPerms')

def reporttermMeasure (preDef : PreDefinition) (recArgPos : Nat) : MetaM Unit := do
  if let some ref := preDef.termination.terminationBy?? then
    let fn ← lambdaTelescope preDef.value fun xs _ => mkLambdaFVars xs xs[recArgPos]!
    let termMeasure : TerminationMeasure:= {ref := .missing, structural := true, fn}
    let arity ← lambdaTelescope preDef.value fun xs _ => pure xs.size
    let stx ← termMeasure.delab arity (extraParams := preDef.termination.extraParams)
    Tactic.TryThis.addSuggestion ref stx


def structuralRecursion (preDefs : Array PreDefinition) (termMeasure?s : Array (Option TerminationMeasure)) : TermElabM Unit := do
  let names := preDefs.map (·.declName)
  let ((recArgPoss, preDefsNonRec, fixedParamPerms), state) ← run <| inferRecArgPos preDefs termMeasure?s
  for recArgPos in recArgPoss, preDef in preDefs do
    reporttermMeasure preDef recArgPos
  state.addMatchers.forM liftM
  preDefsNonRec.forM fun preDefNonRec => do
    let preDefNonRec ← eraseRecAppSyntax preDefNonRec
    -- state.addMatchers.forM liftM
    mapError (f := (m!"structural recursion failed, produced type incorrect term{indentD ·}")) do
      -- We create the `_unsafe_rec` before we abstract nested proofs.
      -- Reason: the nested proofs may be referring to the _unsafe_rec.
      addNonRec preDefNonRec (applyAttrAfterCompilation := false) (all := names.toList)
  let preDefs ← preDefs.mapM (eraseRecAppSyntax ·)
  addAndCompilePartialRec preDefs
  for preDef in preDefs, recArgPos in recArgPoss do
    let mut preDef := preDef
    unless preDef.kind.isTheorem do
      unless (← isProp preDef.type) do
        preDef ← abstractNestedProofs preDef
        /-
        Don't save predefinition info for equation generator
        for theorems and definitions that are propositions.
        See issue #2327
        -/
        registerEqnsInfo preDef (preDefs.map (·.declName)) recArgPos fixedParamPerms
    addSmartUnfoldingDef preDef recArgPos
    markAsRecursive preDef.declName
  for preDef in preDefs do
    -- must happen in separate loop so realizations can see eqnInfos of all other preDefs
    enableRealizationsForConst preDef.declName
    -- must happen after `enableRealizationsForConst`
    generateEagerEqns preDef.declName
  applyAttributesOf preDefsNonRec AttributeApplicationTime.afterCompilation


end Structural

export Structural (structuralRecursion)

end Lean.Elab
