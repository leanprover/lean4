/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Joachim Breitner
-/
prelude
import Lean.Elab.PreDefinition.TerminationArgument
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
    else if !(← vals.allM fun val => return val.bindingName! == vals[0]!.bindingName! && val.binderInfo == vals[0]!.binderInfo && (← isDefEq val.bindingDomain! vals[0]!.bindingDomain!)) then
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

/-- Checks that all parameter types are mutually inductive -/
private def checkAllFromSameClique (recArgInfos : Array RecArgInfo) : MetaM Unit := do
  for recArgInfo in recArgInfos do
    unless recArgInfos[0]!.indAll.contains recArgInfo.indName do
      throwError m!"Cannot use structural mutual recursion: The recursive argument of " ++
        m!"{recArgInfos[0]!.fnName} is of type {recArgInfos[0]!.indName}, " ++
        m!"the recursive argument of {recArgInfo.fnName} is of type " ++
            m!"{recArgInfo.indName}, and these are not mutually recursive."

private def elimMutualRecursion (preDefs : Array PreDefinition) (recArgPoss : Array Nat) : M (Array PreDefinition) := do
  withoutModifyingEnv do
    preDefs.forM (addAsAxiom ·)
    let names := preDefs.map (·.declName)
    let preDefs ← preDefs.mapM fun preDef =>
      return { preDef with value := (← preprocess preDef.value names) }

    -- The syntactically fixed arguments
    let maxNumFixed ← getMutualFixedPrefix preDefs

    -- We do two passes to get the RecArgInfo values.
    -- From the first pass, we only keep the  mininum of the `numFixed` reported.
    let numFixed ← lambdaBoundedTelescope preDefs[0]!.value maxNumFixed fun xs _ => do
      assert! xs.size = maxNumFixed
      let values ← preDefs.mapM (instantiateLambda ·.value xs)

      let recArgInfos ← preDefs.mapIdxM fun i preDef => do
        let recArgPos := recArgPoss[i]!
        let value := values[i]!
        lambdaTelescope value fun ys _value => do
          getRecArgInfo preDef.declName maxNumFixed (xs ++ ys) recArgPos

      return (recArgInfos.map (·.numFixed)).foldl Nat.min maxNumFixed

    if numFixed < maxNumFixed then
      trace[Elab.definition.structural] "Reduced numFixed from {maxNumFixed} to {numFixed}"

    -- Now we bring exactly that `numFixed` parameter into scope.
    lambdaBoundedTelescope preDefs[0]!.value numFixed fun xs _ => do
      assert! xs.size = numFixed
      let values ← preDefs.mapM (instantiateLambda ·.value xs)

      let recArgInfos ← preDefs.mapIdxM fun i preDef => do
        let recArgPos := recArgPoss[i]!
        let value := values[i]!
        lambdaTelescope value fun ys _value => do
          getRecArgInfo preDef.declName numFixed (xs ++ ys) recArgPos

      -- Two passes should suffice
      assert! recArgInfos.all (·.numFixed = numFixed)

      let indInfo ← getConstInfoInduct recArgInfos[0]!.indName
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

      checkAllFromSameClique recArgInfos
      -- Sort the (indices of the) definitions by their position in indInfo.all
      let positions : Array (Array Nat) :=
        indInfo.all.toArray.map fun indName =>
          (Array.range preDefs.size).filter fun i =>
            recArgInfos[i]!.indName = indName
      -- Sanity check: is this really a grouped permutation of all the indices?
      assert! Array.range preDefs.size = positions.flatten.qsort Nat.blt

      -- Construct the common `.brecOn` arguments
      let motives ← (Array.zip recArgInfos values).mapM fun (r, v) => mkBRecOnMotive r v
      let brecOnConst ← mkBRecOnConst recArgInfos positions motives
      let FTypes ← inferBRecOnFTypes recArgInfos positions brecOnConst
      let FArgs ← (recArgInfos.zip  (values.zip FTypes)).mapM fun (r, (v, t)) =>
        mkBRecOnF recArgInfos positions r v t
      -- Assemble the individual `.brecOn` applications
      let valuesNew ← (Array.zip recArgInfos values).mapIdxM fun i (r, v) =>
        mkBrecOnApp positions i brecOnConst FArgs r v
      -- Abstract over the fixed prefixed
      let valuesNew ← valuesNew.mapM (mkLambdaFVars xs ·)
      return (Array.zip preDefs valuesNew).map fun ⟨preDef, valueNew⟩ => { preDef with value := valueNew }

def reportTermArg (preDef : PreDefinition) (recArgPos : Nat) : MetaM Unit := do
  if let some ref := preDef.termination.terminationBy?? then
    let fn ← lambdaTelescope preDef.value fun xs _ => mkLambdaFVars xs xs[recArgPos]!
    let termArg : TerminationArgument:= {ref := .missing, structural := true, fn}
    let arity ← lambdaTelescope preDef.value fun xs _ => pure xs.size
    let stx ← termArg.delab arity (extraParams := preDef.termination.extraParams)
    Tactic.TryThis.addSuggestion ref stx

private def inferRecArgPos (preDefs : Array PreDefinition)
    (termArgs? : Option TerminationArguments) : M (Array Nat × Array PreDefinition) := do
  withoutModifyingEnv do
    if let some termArgs := termArgs? then
      let recArgPoss ← termArgs.mapM (·.structuralArg)
      let preDefsNew ← elimMutualRecursion preDefs recArgPoss
      return (recArgPoss, preDefsNew)
    else
      let #[preDef] := preDefs
        | throwError "mutual structural recursion requires explicit `termination_by` clauses"
      -- Use termination_by annotation to find argument to recurse on, or just try all
      tryAllArgs preDef.value fun i =>
        mapError (f := fun msg => m!"argument #{i+1} cannot be used for structural recursion{indentD msg}") do
          let preDefsNew ← elimMutualRecursion #[preDef] #[i]
          return (#[i], preDefsNew)

def structuralRecursion (preDefs : Array PreDefinition) (termArgs? : Option TerminationArguments) : TermElabM Unit := do
  let ((recArgPoss, preDefsNonRec), state) ← run <| inferRecArgPos preDefs termArgs?
  for recArgPos in recArgPoss, preDef in preDefs do
    reportTermArg preDef recArgPos
  state.addMatchers.forM liftM
  preDefsNonRec.forM fun preDefNonRec => do
    let preDefNonRec ← eraseRecAppSyntax preDefNonRec
    -- state.addMatchers.forM liftM
    mapError (addNonRec preDefNonRec (applyAttrAfterCompilation := false)) fun msg =>
      m!"structural recursion failed, produced type incorrect term{indentD msg}"
    -- We create the `_unsafe_rec` before we abstract nested proofs.
    -- Reason: the nested proofs may be referring to the _unsafe_rec.
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
        registerEqnsInfo preDef (preDefs.map (·.declName)) recArgPos
    addSmartUnfoldingDef preDef recArgPos
    markAsRecursive preDef.declName
  applyAttributesOf preDefsNonRec AttributeApplicationTime.afterCompilation

builtin_initialize
  registerTraceClass `Elab.definition.structural

end Structural

export Structural (structuralRecursion)

end Lean.Elab
