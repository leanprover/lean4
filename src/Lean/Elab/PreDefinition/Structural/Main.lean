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

partial def withCommonTelescope (preDefs : Array PreDefinition) (k : Array Expr → Array Expr → MetaM α) : MetaM α :=
  go #[] (preDefs.map (·.value))
where
  go (fvars : Array Expr) (vals : Array Expr) : MetaM α := do
    if !(vals.all fun val => val.isLambda) then
      k fvars vals
    else if !(← vals.allM fun val => return val.bindingName! == vals[0]!.bindingName! && val.binderInfo == vals[0]!.binderInfo && (← isDefEq val.bindingDomain! vals[0]!.bindingDomain!)) then
      k fvars vals
    else
      withLocalDecl vals[0]!.bindingName! vals[0]!.binderInfo vals[0]!.bindingDomain! fun x =>
        go (fvars.push x) (vals.map fun val => val.bindingBody!.instantiate1 x)

def getMutualFixedPrefix (preDefs : Array PreDefinition) : MetaM Nat :=
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

private def elimMutualRecursion (preDefs : Array PreDefinition) (termArgs : TerminationArguments) : M Unit := do
  withoutModifyingEnv do
    let numFixed ← getMutualFixedPrefix preDefs
    let recArgInfos ← preDefs.mapIdxM fun i preDef => do
      let termArg := termArgs[i]!
      lambdaTelescope preDef.value fun xs _value => do
        let recArgInfo ← withRecArgInfo preDef.declName numFixed xs (← termArg.structuralArg) pure
        return recArgInfo
    let indInfo ← getConstInfoInduct recArgInfos[0]!.indName
    if ← isInductivePredicate indInfo.name then
      throwError "structural mutual recursion over inductive predicates is not yet supported"
    -- TODO: This check should be up to permutation and calculate that permutation somehow
    unless indInfo.all.toArray = recArgInfos.map (·.indName) do
      throwError "structural mutual recursion only supported without reordering for now"



private def elimRecursion (preDef : PreDefinition) (termArg? : Option TerminationArgument) : M (Nat × PreDefinition) := do
  trace[Elab.definition.structural] "{preDef.declName} := {preDef.value}"
  withoutModifyingEnv do lambdaTelescope preDef.value fun xs value => do
    addAsAxiom preDef
    let value ← preprocess value preDef.declName
    trace[Elab.definition.structural] "{preDef.declName} {xs} :=\n{value}"
    let numFixed ← getFixedPrefix preDef.declName xs value
    trace[Elab.definition.structural] "numFixed: {numFixed}"
    let go := fun recArgInfo => do
      let valueNew ← if recArgInfo.indPred then
        let valueNew ← mkIndPredBRecOn recArgInfo xs value
        mkLambdaFVars xs valueNew
      else
        let valueNew ← mkBRecOn recArgInfo (← mkLambdaFVars xs[recArgInfo.fixedParams.size:] value)
        mkLambdaFVars (xs[:recArgInfo.fixedParams.size]) valueNew
      trace[Elab.definition.structural] "result: {valueNew}"
      -- Recursive applications may still occur in expressions that were not visited by replaceRecApps (e.g., in types)
      let valueNew ← ensureNoRecFn preDef.declName valueNew
      return (recArgInfo.recArgPos, { preDef with value := valueNew })
    -- Use termination_by annotation to find argument to recurse on, or just try all
    match termArg? with
    | .some termArg =>
        assert! termArg.structural
        withRecArgInfo preDef.declName numFixed xs (← termArg.structuralArg) go
    | .none => findRecArg preDef.declName numFixed xs go

def reportTermArg (preDef : PreDefinition) (recArgPos : Nat) : MetaM Unit := do
  if let some ref := preDef.termination.terminationBy?? then
    let fn ← lambdaTelescope preDef.value fun xs _ => mkLambdaFVars xs xs[recArgPos]!
    let termArg : TerminationArgument := {ref := .missing, structural := true, fn}
    let arity ← lambdaTelescope preDef.value fun xs _ => pure xs.size
    let stx ← termArg.delab arity (extraParams := preDef.termination.extraParams)
    Tactic.TryThis.addSuggestion ref stx

def structuralRecursion (preDefs : Array PreDefinition) (termArgs? : Option TerminationArguments) : TermElabM Unit := do
  if preDefs.size != 1 then
    let .some termArgs := termArgs?
      | throwError "mutual structural recursion reqiures explicit `termination_by` clauses"
    let (_, _state) ← run <| elimMutualRecursion preDefs termArgs
  else do
    let termArg? := termArgs?.map (·[0]!)
    let ((recArgPos, preDefNonRec), state) ← run <| elimRecursion preDefs[0]! termArg?
    reportTermArg preDefNonRec recArgPos
    let preDefNonRec ← eraseRecAppSyntax preDefNonRec
    let mut preDef ← eraseRecAppSyntax preDefs[0]!
    state.addMatchers.forM liftM
    mapError (addNonRec preDefNonRec (applyAttrAfterCompilation := false)) fun msg =>
      m!"structural recursion failed, produced type incorrect term{indentD msg}"
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
