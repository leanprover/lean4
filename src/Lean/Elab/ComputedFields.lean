/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
module

prelude
public import Lean.Meta.Constructions.CasesOn
public import Lean.Elab.PreDefinition.WF.Eqns
import Lean.Compiler.CSimpAttr
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr
import Lean.Compiler.InductiveOverride

public section

/-!
# Computed fields

Inductives can have computed fields which are recursive functions whose value
is stored in the constructors, and can be accessed in constant time.

```lean
inductive Exp
  | hole
  | app (x y : Exp)
with
  f : Exp → Nat
    | .hole => 42
    | .app x y => f x + f y

-- `Exp.f x` runs in constant time, even if `x` is a dag-like value
```

This file implements the computed fields feature by simulating it via
`implemented_by`.  The main function is `setComputedFields`.
-/

namespace Lean.Elab.ComputedFields
open Meta

/--
Marks a function as a computed field of an inductive.

Computed fields are specified in the with-block of an inductive type declaration. They can be used
to allow certain values to be computed only once at the time of construction and then later be
accessed immediately.

Example:
```
inductive NatList where
  | nil
  | cons : Nat → NatList → NatList
with
  @[computed_field] sum : NatList → Nat
  | .nil => 0
  | .cons x l => x + l.sum
  @[computed_field] length : NatList → Nat
  | .nil => 0
  | .cons _ l => l.length + 1
```
-/
@[builtin_doc]
builtin_initialize computedFieldAttr : TagAttribute ←
  registerTagAttribute `computed_field "Marks a function as a computed field of an inductive" fun _ => do
    unless (← getOptions).getBool `elaboratingComputedFields do
      throwError "The `[computed_field]` attribute can only be used in the with-block of an inductive"

def isScalarField (ctor : Name) : CoreM Bool :=
  return (← getConstInfoCtor ctor).numFields == 0 -- TODO

structure Context extends InductiveVal where
  lparams : List Level
  params : Array Expr
  compFields : Array Name
  compFieldVars : Array Expr
  indices : Array Expr
  val : Expr

abbrev M := ReaderT Context MetaM

-- TODO: doesn't work if match contains patterns like `.app (.app a b) c`
def getComputedFieldValue (computedField : Name) (ctorTerm : Expr) : MetaM Expr := do
  let ctorName := ctorTerm.getAppFn.constName!
  let ind ← getConstInfoInduct (← getConstInfoCtor ctorName).induct
  let val ← mkAppOptM computedField (.replicate (ind.numParams+ind.numIndices) none ++ #[some ctorTerm])
  let val ←
    if let some wfEqn := WF.eqnInfoExt.find? (← getEnv) computedField then
      pure <| mkAppN (wfEqn.value.instantiateLevelParams wfEqn.levelParams val.getAppFn.constLevels!) val.getAppArgs
    else
      unfoldDefinition val
  let val ← whnfHeadPred val (return ctorTerm.occurs ·)
  if !ctorTerm.occurs val then return val
  throwError "computed field {computedField} does not reduce for constructor {ctorName}"

def validateComputedFields : M Unit := do
  let {compFieldVars, indices, val ..} ← read
  for cf in compFieldVars do
    let ty ← inferType cf
    if ty.containsFVar val.fvarId! then
      throwError "computed field {cf}'s type must not depend on value{indentExpr ty}"
    if indices.any (ty.containsFVar ·.fvarId!) then
      throwError "computed field {cf}'s type must not depend on indices{indentExpr ty}"

def mkCtorImplName (nm : Name) : Name :=
  .str nm "_impl"

def mkCasesOnImplName (nm : Name) : Name :=
  .str (mkCasesOnName nm) "_impl"

def mkCtorOverrideName (nm : Name) : Name :=
  .str nm "_override"

def mkCasesOnOverrideName (nm : Name) : Name :=
  .str (mkCasesOnName nm) "_override"

def mkComputedFieldOverrideName (nm : Name) : Name :=
  .str nm "_override"

def mkCasesOnCSimpName (nm : Name) : Name :=
  .str (mkCasesOnName nm) "_csimp"

def mkCasesOnImpl : M Unit := do
  let ctx ← read
  let motiveUniv := (← getConstVal (mkCasesOnName ctx.name)).levelParams.head!
  let inductApp := mkAppN (mkAppN (.const ctx.name ctx.lparams) ctx.params) ctx.indices
  let motiveType ← mkForallFVars ctx.indices (.forallE `t inductApp (.sort (.param motiveUniv)) .default)
  withLocalDecl `motive .implicit motiveType fun motive => do
  withLocalDeclD `t inductApp fun major => do
  let mut altInfos := #[]
  withLocalDeclsDND altInfos fun minors => do
  let res := mkAppN motive ctx.indices
  let type ← mkForallFVars (ctx.params ++ #[motive] ++ ctx.indices ++ #[major] ++ minors) res
  addDecl <| .opaqueDecl {
    name := mkCasesOnImplName ctx.name
    levelParams := motiveUniv :: ctx.levelParams
    type
    -- We don't care about the value since the compiler will not look at it because of the override
    value := .app (.const ``lcUnreachable [← getLevel type]) type
    isUnsafe := true
  }
  let override := .isCases (mkCasesOnImplName ctx.name)
  modifyEnv (Compiler.addInductiveOverride · override)

def mkCtorImpl (ctor : Name) (cidx : Nat) : M Unit := do
  let ctx ← read
  let isScalar ← isScalarField ctor
  let newCtorName := mkCtorImplName ctor
  let ctorType ← inferType (mkAppN (mkConst ctor ctx.lparams) ctx.params)
  let (newCtorType, newCtorValue, numFields) ← forallTelescope ctorType fun fields retTy => do
    let vars := ctx.params ++ (if isScalar then #[] else ctx.compFieldVars) ++ fields
    let ctorApp := mkAppN (mkAppN (.const ctor ctx.lparams) ctx.params) fields
    let type ← mkForallFVars vars retTy
    let value ← mkLambdaFVars vars ctorApp
    return (type, value, fields.size + if isScalar then 0 else ctx.compFieldVars.size)
  addDecl <| .defnDecl {
    name := newCtorName
    levelParams := ctx.levelParams
    type := newCtorType
    value := newCtorValue
    hints := .opaque
    safety := .unsafe
  }
  let override := .constructor newCtorName {
    induct := ctx.name
    numParams := ctx.numParams
    cidx, numFields
  }
  modifyEnv (Compiler.addInductiveOverride · override)

def mkImpls : M Unit := do
  let ctx ← read
  let mut cidx := 0
  for ctor in ctx.ctors do
    mkCtorImpl ctor cidx
    cidx := cidx + 1
  let override := .inductiveType ctx.name {
    numParams := ctx.numParams
    ctors := ctx.ctors.map mkCtorImplName
    isRec := ctx.isRec
  }
  modifyEnv (Compiler.addInductiveOverride · override)
  mkCasesOnImpl

def overrideCasesOn : M Unit := do
  let ctx ← read
  let casesOn ← getConstVal (mkCasesOnName ctx.name)
  let lparams := casesOn.levelParams.map .param
  let value ← forallTelescope (← instantiateForall casesOn.type ctx.params) fun xs _ => do
    let nonMinors := xs[0...(ctx.numIndices+2)].toArray -- parameters, indices and major premise
    let minors := xs[(ctx.numIndices+2)...*].toArray
    let newMinors ← minors.zipWithM (bs := ctx.ctors.toArray) fun minor ctor => do
      forallTelescope (← inferType minor) fun args _ => do
        let newVars := if ← isScalarField ctor then #[] else ctx.compFieldVars
        mkLambdaFVars newVars <| mkAppN minor args
    let casesOnApp := .const (mkCasesOnImplName ctx.name) lparams
    let casesOnApp := mkAppN (mkAppN casesOnApp nonMinors) newMinors
    mkLambdaFVars (ctx.params ++ xs) casesOnApp
  -- we don't need to compile this one because we use `macro_inline`
  addDecl <| .defnDecl {
    name := mkCasesOnOverrideName ctx.name
    levelParams := casesOn.levelParams
    type := casesOn.type
    value
    hints  := .opaque
    safety := .unsafe
  }
  let csimpType := mkApp3 (.const ``Eq [← getLevel casesOn.type]) casesOn.type
    (.const (mkCasesOnName ctx.name) lparams)
    (.const (mkCasesOnOverrideName ctx.name) lparams)
  addDecl <| .defnDecl {
    name := mkCasesOnCSimpName ctx.name
    levelParams := casesOn.levelParams
    type := csimpType
    value := .app (.const ``lcProof []) csimpType
    hints := .opaque
    safety := .unsafe
  }
  -- We need `csimp` + `macro_inline` to make sure that it is inlined in `toLCNF`
  setInlineAttribute (mkCasesOnOverrideName ctx.name) .macroInline
  Compiler.CSimp.add (mkCasesOnCSimpName ctx.name) .global

def overrideConstructors : M Unit := do
  let ctx ← read
  for ctor in ctx.ctors do
    let ctorVal ← getConstVal ctor
    let ctorType ← instantiateForall ctorVal.type ctx.params
    forallTelescope ctorType fun fields _ => do
      let ctorTerm := mkAppN (mkAppN (mkConst ctor ctx.lparams) ctx.params) fields
      let computedFieldVals ←
        -- elaborating a non-exposed def body
        withoutExporting do
          if ← isScalarField ctor then pure #[] else
            ctx.compFields.mapM (getComputedFieldValue · ctorTerm)
      let value := mkConst (mkCtorImplName ctor) ctx.lparams
      let value := mkAppN value ctx.params
      let value := mkAppN value computedFieldVals
      let value := mkAppN value fields
      let value ← mkLambdaFVars (ctx.params ++ fields) value
      let decl : Declaration := .defnDecl {
        name := mkCtorOverrideName ctor
        levelParams := ctx.levelParams
        type := ctorVal.type
        value := value
        hints := .opaque
        safety := .unsafe
      }
      addDecl decl
      setImplementedBy ctor (mkCtorOverrideName ctor)
      if ← isScalarField ctor then setInlineAttribute (mkCtorOverrideName ctor)
      compileDecl decl

def overrideComputedFields : M Unit := do
  let ctx ← read
  for compFieldName in ctx.compFields, compFieldVar in ctx.compFieldVars do
    if isExtern (← getEnv) compFieldName then
      compileDecls #[compFieldName]
      continue
    let minors ←
      -- elaborating a non-exposed def body
      withoutExporting do
        ctx.ctors.toArray.mapM fun ctor => do
          let ctorWithParams := mkAppN (mkConst ctor ctx.lparams) ctx.params
          let ctorType ← inferType ctorWithParams
          forallTelescope ctorType fun fields _ => do
            if ← isScalarField ctor then
              let value ← getComputedFieldValue compFieldName (mkAppN ctorWithParams fields)
              mkLambdaFVars fields value
            else
              mkLambdaFVars (ctx.compFieldVars ++ fields) compFieldVar
    let overrideName := mkComputedFieldOverrideName compFieldName
    let compFieldType ← inferType compFieldVar
    let compFieldUniv ← getLevel compFieldType
    let allVars := ctx.params ++ ctx.indices ++ #[ctx.val]
    let type ← mkForallFVars allVars compFieldType
    let motive ← mkLambdaFVars (ctx.indices.push ctx.val) compFieldType
    let value : Expr := .const (mkCasesOnImplName ctx.name) (compFieldUniv :: ctx.lparams)
    let value := (mkAppN value ctx.params).app motive
    let value := (mkAppN value ctx.indices).app ctx.val
    let value := mkAppN value minors
    let value ← mkLambdaFVars allVars value
    addAndCompile <| .defnDecl {
      name := overrideName
      levelParams := ctx.levelParams
      type, value
      safety := .unsafe
      hints := .opaque
    }
    if let some inlineAttr := Compiler.getInlineAttribute? (← getEnv) compFieldName then
      setInlineAttribute overrideName inlineAttr
    setImplementedBy compFieldName overrideName

def mkComputedFieldOverrides (declName : Name) (compFields : Array Name) : MetaM Unit := do
  let ind ← getConstInfoInduct declName
  let lparams := ind.levelParams.map mkLevelParam
  forallTelescopeReducing ind.type fun paramsIndices _ => do
  withLocalDeclD `self (mkAppN (mkConst ind.name lparams) paramsIndices) fun val => do
    let params := paramsIndices[*...ind.numParams].toArray
    let indices := paramsIndices[ind.numParams...*].toArray
    let compFieldVarInfos ← compFields.mapM fun fieldDeclName => do
      let name := fieldDeclName.replacePrefix declName .anonymous
      let type ← inferType (mkAppN (.const fieldDeclName lparams) (params ++ indices ++ #[val]))
      return (name, type)
    withLocalDeclsDND compFieldVarInfos fun compFieldVars => do
      let ctx := { ind with lparams, params, compFields, compFieldVars, indices, val }
      ReaderT.run (r := ctx) do
        validateComputedFields
        mkImpls
        overrideCasesOn
        overrideConstructors
        overrideComputedFields

/--
Sets the computed fields for a block of mutual inductives, adding the implementation via
`implemented_by` and `csimp`.

The `computedFields` argument contains a pair for every inductive in the mutual block, consisting
of the name of the inductive and the names of the associated computed fields.
-/
def setComputedFields (computedFields : Array (Name × Array Name)) : MetaM Unit := do
  for (indName, computedFieldNames) in computedFields do
    for computedFieldName in computedFieldNames do
      unless computedFieldAttr.hasTag (← getEnv) computedFieldName do
        logError m!"'{computedFieldName}' must be tagged with @[computed_field]"
    mkComputedFieldOverrides indName computedFieldNames
