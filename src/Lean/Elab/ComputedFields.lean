/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
prelude
import Lean.Meta.Constructions.CasesOn
import Lean.Compiler.ImplementedByAttr
import Lean.Elab.PreDefinition.WF.Eqns

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

builtin_initialize computedFieldAttr : TagAttribute ←
  registerTagAttribute `computed_field "Marks a function as a computed field of an inductive" fun _ => do
    unless (← getOptions).getBool `elaboratingComputedFields do
      throwError "The @[computed_field] attribute can only be used in the with-block of an inductive"

def mkUnsafeCastTo (expectedType : Expr) (e : Expr) : MetaM Expr :=
  mkAppOptM ``unsafeCast #[none, expectedType, e]

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

def mkImplType : M Unit := do
  let {name, isUnsafe, type, ctors, levelParams, numParams, lparams, params, compFieldVars, ..} ← read
  addDecl <| .inductDecl levelParams numParams
    (isUnsafe := isUnsafe) -- Note: inlining is disabled with unsafe inductives
    [{ name := name ++ `_impl, type,
       ctors := ← ctors.mapM fun ctor => do
         forallTelescope (← inferType (mkAppN (mkConst ctor lparams) params)) fun fields retTy => do
           let retTy := mkAppN (mkConst (name ++ `_impl) lparams) retTy.getAppArgs
           let type ← mkForallFVars (params ++ (if ← isScalarField ctor then #[] else compFieldVars) ++ fields) retTy
           return { name := ctor ++ `_impl, type } }]

def overrideCasesOn : M Unit := do
  let {name, numIndices, ctors, lparams, params, compFieldVars, ..} ← read
  let casesOn ← getConstInfoDefn (mkCasesOnName name)
  mkCasesOn (name ++ `_impl)
  let value ←
    forallTelescope (← instantiateForall casesOn.type params) fun xs constMotive => do
      let (indices, major, minors) := (xs[1:numIndices+1].toArray,
        xs[numIndices+1]!, xs[numIndices+2:].toArray)
      let majorImplTy := mkAppN (mkConst (name ++ `_impl) lparams) (params ++ indices)
      mkLambdaFVars (params ++ xs) <|
        mkAppN (mkConst (mkCasesOnName (name ++ `_impl))
            (casesOn.levelParams.map mkLevelParam)) <|
        params ++
        #[← withLocalDeclD `a majorImplTy fun majorImpl => do
          withLetDecl `m (← inferType constMotive) constMotive fun m => do
          mkLambdaFVars (#[m] ++ indices ++ #[majorImpl]) m] ++
        indices ++ #[← mkUnsafeCastTo majorImplTy major] ++
        (← (minors.zip ctors.toArray).mapM fun (minor, ctor) => do
          forallTelescope (← inferType minor) fun args _ => do
            mkLambdaFVars ((if ← isScalarField ctor then #[] else compFieldVars) ++ args)
              (← mkUnsafeCastTo constMotive (mkAppN minor args)))
  let nameOverride := mkCasesOnName name ++ `_override
  addDecl <| .defnDecl { casesOn with
    name := nameOverride
    all  := [nameOverride]
    value
    hints  := .opaque
    safety := .unsafe
  }
  setInlineAttribute (mkCasesOnName name ++ `_override)
  setImplementedBy (mkCasesOnName name) (mkCasesOnName name ++ `_override)

def overrideConstructors : M Unit := do
  let {ctors, levelParams, lparams, params, compFields, ..} ← read
  for ctor in ctors do
    forallTelescope (← inferType (mkAppN (mkConst ctor lparams) params)) fun fields retTy => do
    let ctorTerm := mkAppN (mkConst ctor lparams) (params ++ fields)
    let computedFieldVals ← if ← isScalarField ctor then pure #[] else
      compFields.mapM (getComputedFieldValue · ctorTerm)
    addDecl <| .defnDecl {
      name := ctor ++ `_override
      levelParams
      type := ← inferType (mkConst ctor lparams)
      value := ← mkLambdaFVars (params ++ fields) <| ← mkUnsafeCastTo retTy <|
        mkAppN (mkConst (ctor ++ `_impl) lparams) (params ++ computedFieldVals ++ fields)
      hints := .opaque
      safety := .unsafe
    }
    setImplementedBy ctor (ctor ++ `_override)
    if ← isScalarField ctor then setInlineAttribute (ctor ++ `_override)

def overrideComputedFields : M Unit := do
  let {name, levelParams, ctors, compFields, compFieldVars, lparams, params, indices, val ..} ← read
  withLocalDeclD `x (mkAppN (mkConst (name ++ `_impl) lparams) (params ++ indices)) fun xImpl => do
  for cfn in compFields, cf in compFieldVars do
    if isExtern (← getEnv) cfn then
      compileDecls [cfn]
      continue
    let cases ← ctors.toArray.mapM fun ctor => do
      forallTelescope (← inferType (mkAppN (mkConst ctor lparams) params)) fun fields _ => do
      if ← isScalarField ctor then
        mkLambdaFVars fields <|
          ← getComputedFieldValue cfn (mkAppN (mkConst ctor lparams) (params ++ fields))
      else
        mkLambdaFVars (compFieldVars ++ fields) cf
    addDecl <| .defnDecl {
      name := cfn ++ `_override
      levelParams
      type := ← mkForallFVars (params ++ indices ++ #[val]) (← inferType cf)
      value := ← mkLambdaFVars (params ++ indices ++ #[val]) <|
        ← mkAppOptM (mkCasesOnName (name ++ `_impl))
          ((params ++ #[← mkLambdaFVars (indices.push xImpl) (← inferType cf)] ++ indices ++
            #[← mkUnsafeCastTo (← inferType xImpl) val] ++ cases).map some)
      safety := .unsafe
      hints := .opaque
    }
    setImplementedBy cfn (cfn ++ `_override)

def mkComputedFieldOverrides (declName : Name) (compFields : Array Name) : MetaM Unit := do
  let ind ← getConstInfoInduct declName
  if ind.ctors.length < 2 then
    throwError "computed fields require at least two constructors"
  let lparams := ind.levelParams.map mkLevelParam
  forallTelescope ind.type fun paramsIndices _ => do
  withLocalDeclD `x (mkAppN (mkConst ind.name lparams) paramsIndices) fun val => do
    let params := paramsIndices[:ind.numParams].toArray
    let indices := paramsIndices[ind.numParams:].toArray
    let compFieldVars := compFields.map fun fieldDeclName =>
      (fieldDeclName.updatePrefix .anonymous,
        fun _ => do inferType (← mkAppM fieldDeclName (params ++ indices ++ #[val])))
    withLocalDeclsD compFieldVars fun compFieldVars => do
      let ctx := { ind with lparams, params, compFields, compFieldVars, indices, val }
      ReaderT.run (r := ctx) do
        validateComputedFields
        mkImplType
        overrideCasesOn
        overrideConstructors
        overrideComputedFields

/--
Sets the computed fields for a block of mutual inductives,
adding the implementation via `implemented_by`.

The `computedFields` argument contains a pair
for every inductive in the mutual block,
consisting of the name of the inductive
and the names of the associated computed fields.
-/
def setComputedFields (computedFields : Array (Name × Array Name)) : MetaM Unit := do
  for (indName, computedFieldNames) in computedFields do
    for computedFieldName in computedFieldNames do
      unless computedFieldAttr.hasTag (← getEnv) computedFieldName do
        logError m!"'{computedFieldName}' must be tagged with @[computed_field]"
    mkComputedFieldOverrides indName computedFieldNames

  -- Once all the implemented_by infrastructure is set up, compile everything.
  compileDecls <| computedFields.toList.map fun (indName, _) =>
    mkCasesOnName indName ++ `_override

  let mut toCompile := #[]
  for (declName, computedFields) in computedFields do
    let ind ← getConstInfoInduct declName
    for ctor in ind.ctors do
      toCompile := toCompile.push (ctor ++ `_override)
    for fieldName in computedFields do
      unless isExtern (← getEnv) fieldName do
        toCompile := toCompile.push <| fieldName ++ `_override
  compileDecls toCompile.toList
