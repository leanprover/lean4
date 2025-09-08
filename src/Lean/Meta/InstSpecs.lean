/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

module
prelude
public import Init.System.IO
public import Lean.Attributes
import Lean.Meta.Basic
import Lean.Structure
import Lean.Meta.CtorRecognizer
import Lean.Meta.InferType
import Lean.Meta.AppBuilder
import Lean.ReservedNameAction

namespace Lean

open Meta

structure InstSpecsInfo where
  clsName : Name
  /-- Array mapping field names to implementation functions. -/
  fieldImpls : Array (Name × Name)
  /-- rewrite rules to apply -/
  thms  : Array Expr

/--
This function checks the `instName` for eligibility and collects the information to rewrite.
It is run twice: when setting the `@[specs]` attribute as a preflight check, and when actually realizing
the constants.
-/
def getInstSpecsInfo (instName : Name) : MetaM InstSpecsInfo := do
  let instInfo ← getConstInfoDefn instName
  let some clsName ← isClass? instInfo.type
    | throwError "expected `{.ofConstName instName}` to be a type class instance, but its's \
         type{inlineExpr instInfo.type}does not look like a class."
  let instArity ← forallTelescopeReducing instInfo.type fun xs _ => pure xs.size
  let some structInfo := getStructureInfo? (← getEnv) clsName
    | throwError "`{.ofConstName clsName}` is not a structure"

  lambdaTelescope instInfo.value fun xs body => do
    let inst := mkAppN (mkConst instInfo.name (instInfo.levelParams.map mkLevelParam)) xs
    let clsApp ← instantiateForall instInfo.type xs
    unless xs.size == instArity && (← isConstructorApp body) do
      throwError "the definition of `{.ofConstName instName}` does not have the expected shape"

    let mut fieldImpls := #[]
    let mut thms := #[]

    for field in structInfo.fieldNames, arg in body.getAppArgsN structInfo.fieldNames.size do
      if (← isProof arg) then continue
      let arg := arg.eta
      let f := arg.getAppFn
      let ys := arg.getAppArgs
      unless f.isConst do
        throwError "field `{field}` of the instance is not an application of a constant"
      unless xs == ys do
        throwError "function `{f}` does not take its arguments in the same order as the instance"
      -- Construct the replacement theorems
      let some fieldInfo := getFieldInfo? (← getEnv) clsName field
        | throwError "internal error: could not find field {field} in structure {clsName}"
      let lhs := arg
      let projFn := mkConst fieldInfo.projFn clsApp.getAppFn.constLevels!
      let rhs := mkAppN projFn (clsApp.getAppArgs ++ #[inst])
      let eq ← mkEq lhs rhs
      let thm ← mkForallFVars xs eq
      unless (← isDefEq lhs rhs) do
        throwError "internal error: equation `{eq}` does not hold definitionally"
      fieldImpls := fieldImpls.push (field, f.constName!)
      thms := thms.push thm
    trace[Meta.InstSpecs] "instSpecs for {instName}:\n{fieldImpls}\nthms: {thms}"

    return {clsName, fieldImpls, thms}

public structure InstSpecsAttrData where
  clsName : Name
deriving Inhabited

def getParam (instName : Name) (_stx : Syntax) : AttrM InstSpecsAttrData := do
  -- Preflight check
  let specsInfo ← (getInstSpecsInfo instName).run'
  return {
    clsName := specsInfo.clsName
  }

/--
TODO
-/
@[builtin_doc]
builtin_initialize instSpecsAttr : ParametricAttribute InstSpecsAttrData ←
  registerParametricAttribute {
    name := `specs
    descr := "generate specialization theorem"
    getParam
  }


def startsWithFollowedByNumber (s p : String) : Bool :=
  s.startsWith p && (s.drop p.length).isNat

def isSpecThmNameFor (env : Environment) (name : Name) : Option Name := do
  let .str p n := name | none
  let attrData ← instSpecsAttr.getParam? env p
  for fieldName in getStructureFields env attrData.clsName do
    if n == s!"{fieldName}_spec" || startsWithFollowedByNumber n s!"{fieldName}_spec_" then
      return p
  none


builtin_initialize
  registerReservedNamePredicate fun env name => isSpecThmNameFor env name |>.isSome

  registerReservedNameAction fun name => do
    if let some _instName := isSpecThmNameFor (← getEnv) name then
      throwError "TODO"
    return false


builtin_initialize
   Lean.registerTraceClass `Meta.InstSpecs
