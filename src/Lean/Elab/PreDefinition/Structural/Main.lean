/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Joachim Breitner
-/
module

prelude
public import Lean.Elab.PreDefinition.Mutual
public import Lean.Elab.PreDefinition.Structural.FindRecArg
public import Lean.Elab.PreDefinition.Structural.Preprocess
public import Lean.Elab.PreDefinition.Structural.BRecOn
public import Lean.Elab.PreDefinition.Structural.IndPred
public import Lean.Elab.PreDefinition.Structural.Eqns
public import Lean.Elab.PreDefinition.Structural.SmartUnfolding
public import Lean.Meta.Tactic.TryThis

public section

namespace Lean.Elab
namespace Structural
open Meta

private def elimMutualRecursion (preDefs : Array PreDefinition) (fixedParamPerms : FixedParamPerms)
    (xs : Array Expr) (recArgInfos : Array RecArgInfo) : M (Array PreDefinition) := do
  let values ← preDefs.mapIdxM (fixedParamPerms.perms[·]!.instantiateLambda ·.value xs)
  let indInfo ← getConstInfoInduct recArgInfos[0]!.indGroupInst.all[0]!

  -- Groups the (indices of the) definitions by their position in indInfo.all
  let positions : Positions := .groupAndSort (·.indIdx) recArgInfos (Array.range indInfo.numTypeFormers)
  trace[Elab.definition.structural] "assignments of type formers of {indInfo.name} to functions: {positions}"

  let isIndPred ← isInductivePredicate indInfo.name

  let withFunTypesAndMotives (k : Array Expr → Array Expr → M (Array PreDefinition)) :
      M (Array PreDefinition) := do
    if isIndPred then
      withFunTypes values fun funTypes => do
        let motives ← recArgInfos.mapIdxM fun idx r =>
          mkIndPredBRecOnMotive r values[idx]! funTypes[idx]!
        k funTypes motives
    else
      let motives ← recArgInfos.zipWithM (bs := values) fun r v => mkBRecOnMotive r v
      k #[] motives
  withFunTypesAndMotives fun funTypes motives => do
  trace[Elab.definition.structural] "funTypes: {funTypes}, motives: {motives}"

  let brecOnConst ← mkBRecOnConst recArgInfos positions motives isIndPred
  let FTypes ← inferBRecOnFTypes recArgInfos positions brecOnConst
  trace[Elab.definition.structural] "FTypes: {FTypes}"

  let FArgs ← recArgInfos.mapIdxM fun idx r =>
    let v := values[idx]!
    let t := FTypes[idx]!
    if isIndPred then
      mkIndPredBRecOnF recArgInfos positions r v t (brecOnConst 0).getAppArgs
    else
      mkBRecOnF recArgInfos positions r v t
  trace[Elab.definition.structural] "FArgs: {FArgs}"
  let brecOn := brecOnConst 0
  -- the indices and the major premise are not mentioned in the minor premises
  -- so using `default` is fine here
  let brecOn := mkAppN brecOn (.replicate (indInfo.numIndices + 1) default)
  let packedFTypes ← inferArgumentTypesN positions.size brecOn
  let packedFArgs ← positions.mapMwith (PProdN.mkLambdas · ·) packedFTypes FArgs
  trace[Elab.definition.structural] "packedFArgs: {packedFArgs}"

  -- Assemble the individual `.brecOn` applications
  let valuesNew ← (Array.zip recArgInfos values).mapIdxM fun i (r, v) => do
    mkBRecOnApp positions i brecOnConst packedFArgs funTypes r v
  -- Abstract over the fixed prefixed, preserving the original parameter order
  let valuesNew ← (values.zip valuesNew).mapIdxM fun i ⟨value, valueNew⟩ =>
    lambdaTelescope value fun ys _ => do
      -- NB: Do not eta-contract here, other code (e.g. FunInd) expects this to have the
      -- same number of head lambdas as the original definition
      mkLambdaFVars (fixedParamPerms.perms[i]!.buildArgs xs ys) (valueNew.beta ys)
  return preDefs.zipWith (bs := valuesNew) fun preDef valueNew => { preDef with value := valueNew }

private def inferRecArgPos (preDefs : Array PreDefinition) (termMeasure?s : Array (Option TerminationMeasure)) :
    M (Array Nat × Array PreDefinition × FixedParamPerms) := do
  withoutModifyingEnv do
    preDefs.forM (addAsAxiom ·)
    let fnNames := preDefs.map (·.declName)
    let numSectionVars := preDefs[0]!.numSectionVars
    let preDefs ← preDefs.mapM fun preDef =>
      return { preDef with value := (← preprocess preDef.value fnNames numSectionVars) }
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

def reportTermMeasure (preDef : PreDefinition) (recArgPos : Nat) : MetaM Unit := do
  if let some ref := preDef.termination.terminationBy?? then
    let fn ← lambdaTelescope preDef.value fun xs _ => mkLambdaFVars xs xs[recArgPos]!
    let termMeasure : TerminationMeasure:= {ref := .missing, structural := true, fn}
    let arity ← lambdaTelescope preDef.value fun xs _ => pure xs.size
    let stx ← termMeasure.delab arity (extraParams := preDef.termination.extraParams)
    Tactic.TryThis.addSuggestion ref stx

def structuralRecursion
    (docCtx : LocalContext × LocalInstances) (preDefs : Array PreDefinition)
    (termMeasure?s : Array (Option TerminationMeasure)) :
    TermElabM Unit := do
  let names := preDefs.map (·.declName)
  let ((recArgPoss, preDefsNonRec, fixedParamPerms), state) ← run <| inferRecArgPos preDefs termMeasure?s
  for recArgPos in recArgPoss, preDef in preDefs do
    reportTermMeasure preDef recArgPos
  state.addMatchers.forM liftM
  preDefsNonRec.forM fun preDefNonRec => do
    let preDefNonRec ← eraseRecAppSyntax preDefNonRec
    prependError m!"structural recursion failed, produced type incorrect term" do
      -- We create the `_unsafe_rec` before we abstract nested proofs.
      -- Reason: the nested proofs may be referring to the _unsafe_rec.
      addNonRec docCtx preDefNonRec (applyAttrAfterCompilation := false) (all := names.toList) (isRecursive := true)
  let preDefs ← preDefs.mapM (eraseRecAppSyntax ·)
  addAndCompilePartialRec docCtx preDefs
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
    addSmartUnfoldingDef docCtx preDef recArgPos
  for preDef in preDefs do
    -- must happen in separate loop so realizations can see eqnInfos of all other preDefs
    enableRealizationsForConst preDef.declName
    -- must happen after `enableRealizationsForConst`
    generateEagerEqns preDef.declName
  applyAttributesOf preDefsNonRec AttributeApplicationTime.afterCompilation


end Structural

export Structural (structuralRecursion)

end Lean.Elab
