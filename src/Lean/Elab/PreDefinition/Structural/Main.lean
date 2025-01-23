/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Joachim Breitner
-/
prelude
import Lean.Elab.PreDefinition.TerminationMeasure
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

def getMutualFixedPrefix (preDefs : Array PreDefinition) : M Nat :=
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

private def elimMutualRecursion (preDefs : Array PreDefinition) (xs : Array Expr)
    (recArgInfos : Array RecArgInfo) : M (Array PreDefinition) := do
  let values ← preDefs.mapM (instantiateLambda ·.value xs)
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
    let valueNew ← mkLambdaFVars xs valueNew
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
  -- Abstract over the fixed prefixed
  let valuesNew ← valuesNew.mapM (mkLambdaFVars xs ·)
  return (Array.zip preDefs valuesNew).map fun ⟨preDef, valueNew⟩ => { preDef with value := valueNew }

private def inferRecArgPos (preDefs : Array PreDefinition) (termMeasure?s : Array (Option TerminationMeasure)) :
    M (Array Nat × (Array PreDefinition) × Nat) := do
  withoutModifyingEnv do
    preDefs.forM (addAsAxiom ·)
    let fnNames := preDefs.map (·.declName)
    let preDefs ← preDefs.mapM fun preDef =>
      return { preDef with value := (← preprocess preDef.value fnNames) }

    -- The syntactically fixed arguments
    let maxNumFixed ← getMutualFixedPrefix preDefs

    lambdaBoundedTelescope preDefs[0]!.value maxNumFixed fun xs _ => do
      assert! xs.size = maxNumFixed
      let values ← preDefs.mapM (instantiateLambda ·.value xs)

      tryAllArgs fnNames xs values termMeasure?s fun recArgInfos => do
        let recArgPoss := recArgInfos.map (·.recArgPos)
        trace[Elab.definition.structural] "Trying argument set {recArgPoss}"
        let numFixed := recArgInfos.foldl (·.min ·.numFixed) maxNumFixed
        if numFixed < maxNumFixed then
          trace[Elab.definition.structural] "Reduced numFixed from {maxNumFixed} to {numFixed}"
        -- We may have decreased the number of arguments we consider fixed, so update
        -- the recArgInfos, remove the extra arguments from local environment, and recalculate value
        let recArgInfos := recArgInfos.map ({· with numFixed := numFixed })
        withErasedFVars (xs.extract numFixed xs.size |>.map (·.fvarId!)) do
          let xs := xs[:numFixed]
          let preDefs' ← elimMutualRecursion preDefs xs recArgInfos
          return (recArgPoss, preDefs', numFixed)

def reporttermMeasure (preDef : PreDefinition) (recArgPos : Nat) : MetaM Unit := do
  if let some ref := preDef.termination.terminationBy?? then
    let fn ← lambdaTelescope preDef.value fun xs _ => mkLambdaFVars xs xs[recArgPos]!
    let termMeasure : TerminationMeasure:= {ref := .missing, structural := true, fn}
    let arity ← lambdaTelescope preDef.value fun xs _ => pure xs.size
    let stx ← termMeasure.delab arity (extraParams := preDef.termination.extraParams)
    Tactic.TryThis.addSuggestion ref stx


def structuralRecursion (preDefs : Array PreDefinition) (termMeasure?s : Array (Option TerminationMeasure)) : TermElabM Unit := do
  let names := preDefs.map (·.declName)
  let ((recArgPoss, preDefsNonRec, numFixed), state) ← run <| inferRecArgPos preDefs termMeasure?s
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
        registerEqnsInfo preDef (preDefs.map (·.declName)) recArgPos numFixed
    addSmartUnfoldingDef preDef recArgPos
    markAsRecursive preDef.declName
    generateEagerEqns preDef.declName
  applyAttributesOf preDefsNonRec AttributeApplicationTime.afterCompilation


end Structural

export Structural (structuralRecursion)

end Lean.Elab
