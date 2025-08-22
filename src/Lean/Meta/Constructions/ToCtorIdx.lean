/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Joachim Breitner
-/

module

prelude
public import Lean.Meta.Basic
import Lean.AddDecl
import Lean.Meta.AppBuilder
import Lean.Meta.CompletionName
import Lean.Meta.Injective

open Lean Meta

register_builtin_option genToCtorIdx : Bool := {
  defValue := true
  descr    := "generate the `toCtorIdx` functions for inductive datatypes"
}

public def mkToCtorIdxName (indName : Name) : Name :=
  Name.mkStr indName "toCtorIdx"

/--
For an inductive type `T` with more than one function builds a function `T.toCtorIdx : T → Nat` that
returns the constructor index of the given value.
Does nothing if `T` does not eliminate into `Type` or if `T` is unsafe.
Assumes `T.casesOn` to be defined already.
-/
public def mkToCtorIdx (indName : Name) : MetaM Unit := do
  prependError m!"failed to construct `T.toCtorIdx` for `{.ofConstName indName}`:" do
    unless genToCtorIdx.get (← getOptions) do return
    unless genInjectivity.get (← getOptions)  do return
    let ConstantInfo.inductInfo info ← getConstInfo indName | unreachable!
    if (← isPropFormerType info.type) then return
    let casesOnName := mkCasesOnName indName
    let casesOnInfo ← getConstInfo casesOnName
    unless casesOnInfo.levelParams.length > info.levelParams.length do return

    let us := info.levelParams.map mkLevelParam
    let declName := mkToCtorIdxName indName
    forallBoundedTelescope info.type (info.numParams + info.numIndices) fun xs _ => do
      withNewBinderInfos (xs.map (⟨·.fvarId!, .implicit⟩)) do
      let params : Array Expr := xs[:info.numParams]
      let indices : Array Expr := xs[info.numParams:]
      let indType := mkAppN (mkConst indName us) xs
      let natType  := mkConst ``Nat
      let declType ← mkArrow indType natType
      let declType ← mkForallFVars xs declType
      let declValue ← withLocalDeclD `x indType fun x => do
        let motive ← mkLambdaFVars (indices.push x) natType
        let mut value := mkConst casesOnName (levelOne::us)
        value := mkAppN value params
        value := mkApp value motive
        value := mkAppN value indices
        value := mkApp value x
        for c in info.ctors do
          let cInfo ← getConstInfoCtor c
          let cType ← instantiateForall cInfo.type params
          let alt ← forallBoundedTelescope cType cInfo.numFields fun ys _ =>
            mkLambdaFVars ys <| mkRawNatLit cInfo.cidx
          value := mkApp value alt
        mkLambdaFVars (xs.push x) value
      addAndCompile (.defnDecl (← mkDefinitionValInferringUnsafe
        (name        := declName)
        (levelParams := info.levelParams)
        (type        := declType)
        (value       := declValue)
        (hints       := ReducibilityHints.abbrev)
      ))
      modifyEnv fun env => addToCompletionBlackList env declName
      modifyEnv fun env => addProtected env declName
      setReducibleAttribute declName
