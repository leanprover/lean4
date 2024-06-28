/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
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

private def elimMutualRecursion (preDefs : Array PreDefinition) (recArgPoss : Array Nat) : M (Array PreDefinition) := do
  withoutModifyingEnv do
    preDefs.forM (addAsAxiom ·)
    let names := preDefs.map (·.declName)
    let preDefs ← preDefs.mapM fun preDef =>
      return { preDef with value := (← preprocess preDef.value names) }
    let numFixed ← getMutualFixedPrefix preDefs
    -- Get (only!) the fixed parameters into scope
    lambdaTelescopeBounded preDefs[0]!.value numFixed fun xs _ => do
      assert! xs.size = numFixed
      let values ← preDefs.mapM (instantiateLambda ·.value xs)

      let recArgInfos ← preDefs.mapIdxM fun i preDef => do
        let recArgPos := recArgPoss[i]!
        let value := values[i]!
        lambdaTelescope value fun ys _value => do
          let recArgInfo ← withRecArgInfo preDef.declName numFixed (xs ++ ys) recArgPos pure
          return recArgInfo
      let indInfo ← getConstInfoInduct recArgInfos[0]!.indName
      if ← isInductivePredicate indInfo.name then
        -- Here we branch off to the IndPred construction, but only for non-mutual functions
        unless preDefs.size = 1 do
          throwError "structural mutual recursion over inductive predicates is not supported"
        trace[Elab.definition.structural] "Using mkIndPred construction"
        let preDef := preDefs[0]!
        let recArgInfo := recArgInfos[0]!
        let valueNew ← lambdaTelescope values[0]! fun ys value => do
          let valueNew ← mkIndPredBRecOn recArgInfo (xs ++ ys) value
          mkLambdaFVars (xs ++ ys) valueNew
        trace[Elab.definition.structural] "Nonrecursive value:{indentExpr valueNew}"
        check valueNew
        return #[{ preDef with value := valueNew }]

      -- TODO: This check should be up to permutation and calculate that permutation somehow
      unless indInfo.all.toArray = recArgInfos.map (·.indName) do
        throwError "structural mutual recursion only supported without reordering for now"

      -- Construct the common `.brecOn` arguments
      let motives ← (Array.zip recArgInfos values).mapM fun (r, v) => mkBRecOnMotive r v
      let brecOnConst ← mkBRecOnConst recArgInfos motives
      let FTypes ← inferBRecOnFTypes recArgInfos motives brecOnConst
      let FArgs ← (recArgInfos.zip  (values.zip FTypes)).mapM fun (r, (v, t)) => mkBRecOnF recArgInfos r v t
      -- Assemble the individual `.brecOn` applications
      let valuesNew ← (Array.zip recArgInfos values).mapM fun (r, v) =>
        mkBrecOnApp brecOnConst motives FArgs r v
      -- Abstract over the fixed prefixed
      let valuesNew ← valuesNew.mapM (mkLambdaFVars xs ·)
      return (Array.zip preDefs valuesNew).map fun ⟨preDef, valueNew⟩ => { preDef with value := valueNew }

def buildTermArg (preDef : PreDefinition) (recArgPos : Nat) : MetaM TerminationArgument := do
  let fn ← lambdaTelescope preDef.value fun xs _ => mkLambdaFVars xs xs[recArgPos]!
  return {ref := .missing, structural := true, fn}

def reportTermArg (preDef : PreDefinition) (recArgPos : Nat) : MetaM Unit := do
  if let some ref := preDef.termination.terminationBy?? then
    let termArg ← buildTermArg preDef recArgPos
    let arity ← lambdaTelescope preDef.value fun xs _ => pure xs.size
    let stx ← termArg.delab arity (extraParams := preDef.termination.extraParams)
    Tactic.TryThis.addSuggestion ref stx


private def elimRecursion (preDef : PreDefinition) (termArg? : Option TerminationArgument) : M (Nat × PreDefinition) := do
  trace[Elab.definition.structural] "{preDef.declName} := {preDef.value}"
  withoutModifyingEnv do
    let go := fun i => do
      mapError (f := fun msg => m!"argument #{i+1} cannot be used for structural recursion{indentD msg}") do
        -- Use the mutual inductive case here to exercise ist
        let preDefsNew ← elimMutualRecursion #[preDef] #[i]
        return (i, preDefsNew[0]!)
    -- Use termination_by annotation to find argument to recurse on, or just try all
    match termArg? with
    | .some termArg => go (← termArg.structuralArg)
    | .none => tryAllArgs preDef.value go

def structuralRecursion (preDefs : Array PreDefinition) (termArgs? : Option TerminationArguments) : TermElabM Unit := do
  if preDefs.size != 1 then
    let .some termArgs := termArgs?
      | throwError "mutual structural recursion reqiures explicit `termination_by` clauses"
    let recArgPoss ← termArgs.mapM (·.structuralArg)
    let (preDefsNonRec, state) ← run <| elimMutualRecursion preDefs recArgPoss
    -- TODO: reportTermArg
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
          registerEqnsInfo preDef recArgPos
      addSmartUnfoldingDef preDef recArgPos
      markAsRecursive preDef.declName
    applyAttributesOf preDefsNonRec AttributeApplicationTime.afterCompilation
  else do
    let termArg? := termArgs?.map (·[0]!)
    let ((recArgPos, preDefNonRec), state) ← run <| elimRecursion preDefs[0]! termArg?
    state.addMatchers.forM liftM
    reportTermArg preDefNonRec recArgPos
    let preDefNonRec ← eraseRecAppSyntax preDefNonRec
    mapError (addNonRec preDefNonRec (applyAttrAfterCompilation := false)) fun msg =>
      m!"structural recursion failed, produced type incorrect term{indentD msg}"
    let mut preDef ← eraseRecAppSyntax preDefs[0]!
    -- We create the `_unsafe_rec` before we abstract nested proofs.
    -- Reason: the nested proofs may be referring to the _unsafe_rec.
    addAndCompilePartialRec #[preDef]
    unless preDef.kind.isTheorem do
      unless (← isProp preDef.type) do
        preDef ← abstractNestedProofs preDef
        /-
        Don't save predefinition info for equation generator
        for theorems and definitions that are propositions.
        See issue #2327
        -/
        registerEqnsInfo preDef recArgPos
    addSmartUnfoldingDef preDef recArgPos
    markAsRecursive preDef.declName
    applyAttributesOf #[preDefNonRec] AttributeApplicationTime.afterCompilation

builtin_initialize
  registerTraceClass `Elab.definition.structural

end Structural

export Structural (structuralRecursion)

end Lean.Elab
