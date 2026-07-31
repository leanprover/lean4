/-
Copyright (c) 2026 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module
prelude
public import Lean.ProjFns
public import Lean.Structure
public import Lean.Meta.CasesInfo

public section

namespace Lean.Compiler

/--
Information about an inductive relevant to the compiler
-/
structure InductiveOverrideInfo where
  numParams : Nat
  ctors : List Name
  isRec : Bool
deriving Inhabited

/--
Information about a constructor relevant to the compiler
-/
structure CtorOverrideInfo where
  induct : Name
  cidx : Nat
  numParams : Nat
  numFields : Nat
deriving Inhabited

/--
Description of how the purpose of a declaration deviates from its default purpose.
-/
inductive InductiveOverride where
  /--
  If `typeName` is an inductive, make it instead behave like an `opaque`.
  Also, use the provided `impureType` as the impure type instead of just `tobject`.
  -/
  | simpleType (typeName : Name) (impureType : Expr)
  /--
  Make `typeName` behave like an inductive type with the specified constructors. The specified
  constructors may themselves be ordinary functions but should have `constructor` overrides.

  If `isRec` is false, then it is assumed that traversing constructor types will not loop.
  This is used to test whether a type can have a trivial structure.
  -/
  | inductiveType (typeName : Name) (info : InductiveOverrideInfo)
  /--
  Make `ctorName` behave like a constructor for the type `typeName` with the specified constructor
  index, amount of parameters and amount of fields. The type may or may not be an inductive type
  but should have an `inductiveType` override.
  -/
  | constructor (ctorName : Name) (info : CtorOverrideInfo)
  /--
  Make `elimName` behave like a cases eliminator. This marker is used in place of `isCasesOnLike`
  if the corresponding type is a type with an `inductiveType` override.
  -/
  | isCases (elimName : Name)
  /--
  Make `projName` behave like a projection with the specified information.
  -/
  | projFn (projName : Name) (info : ProjectionFunctionInfo)
deriving Inhabited

/-- The name of the declaration whose purpose is being overridden. -/
@[inline] def InductiveOverride.name : InductiveOverride → Name
  | .simpleType name .. => name
  | .inductiveType name .. => name
  | .constructor name .. => name
  | .isCases name .. => name
  | .projFn name .. => name

builtin_initialize inductiveOverrideExt :
    PersistentEnvExtension InductiveOverride InductiveOverride (NameMap InductiveOverride) ←
  registerPersistentEnvExtension {
    mkInitial := pure {}
    addEntryFn map x := map.insert x.name x
    addImportedFn _ := pure {}
    exportEntriesFn map := map.valuesArray.qsort fun a b => a.name.quickLt b.name
    replay? := some fun _ newState newConsts s =>
      newConsts.foldl (init := s) fun s c =>
        if let some a := newState.find? c then
          s.insert c a
        else s
  }

def addInductiveOverride (env : Environment) (override : InductiveOverride) : Environment :=
  have : Inhabited Environment := ⟨env⟩
  if let some modIdx := env.getModuleIdxFor? override.name then -- See comment at `MapDeclarationExtension`
    panic! s!"cannot add an inductive override for `{override.name}`, \
      it is not defined in the current module but in `{env.allImportedModuleNames[modIdx]!}`"
  else
    inductiveOverrideExt.addEntry (asyncDecl := override.name) env override

def getInductiveOverride? (env : Environment) (declName : Name) : Option InductiveOverride :=
  match env.getModuleIdxFor? declName with
  | some modIdx =>
    let entries := inductiveOverrideExt.getModuleEntries (level := .exported) env modIdx
    entries.binSearch (.simpleType declName default) (fun a b => Name.quickLt a.name b.name)
  | none =>
    (inductiveOverrideExt.getState (asyncDecl := declName) env).find? declName

def hasInductiveOverride (env : Environment) (declName : Name) : Bool :=
  match env.getModuleIdxFor? declName with
  | some modIdx =>
    let entries := inductiveOverrideExt.getModuleEntries (level := .exported) env modIdx
    entries.binSearchContains (.simpleType declName default) (fun a b => Name.quickLt a.name b.name)
  | none =>
    (inductiveOverrideExt.getState (asyncDecl := declName) env).contains declName

private def casesEliminatorInduct (type : Expr) : Name := Id.run do
  let depth := type.getForallArity
  let .bvar discrIdx := type.getForallBody.appArg! | unreachable!
  let .forallE _ t _ _ := type.getForallBodyMaxDepth (depth - discrIdx - 1) | unreachable!
  let indTypeName := t.getAppFn.constName!
  indTypeName

@[inline]
def getCasesInfoOverride? (declName : Name) : CoreM (Option CasesInfo) := do
  if let some (.isCases _) := getInductiveOverride? (← getEnv) declName then
    return ← getCasesInfo declName
  if isSparseCasesOn (← getEnv) declName then
    return ← getCasesInfo declName
  unless isCasesOnRecursor (← getEnv) declName do
    return none
  let info ← getCasesInfo declName
  if hasInductiveOverride (← getEnv) info.indName && !isStructure (← getEnv) info.indName then
    return none
  return info

@[inline]
def isCasesOnLikeOverride (env : Environment) (declName : Name) : Bool := Id.run do
  if let some (.isCases _) := getInductiveOverride? env declName then
    return true
  if isSparseCasesOn env declName then
    return true
  unless isCasesOnRecursor env declName do
    return false
  let some val := env.findConstVal? declName | return false
  let indName := casesEliminatorInduct val.type
  return !hasInductiveOverride env indName || isStructure env indName

@[inline]
def getProjectionFnInfoOverride? (env : Environment) (declName : Name) : Option ProjectionFunctionInfo := do
  if let some (.projFn _ info) := getInductiveOverride? env declName then
    return info
  let info ← env.getProjectionFnInfo? declName
  let .ctorInfo cinfo ← env.find? info.ctorName | none
  if hasInductiveOverride env cinfo.induct then none
  return info

@[inline]
def isProjectionFnOverride (env : Environment) (declName : Name) : Bool :=
  (getProjectionFnInfoOverride? env declName).isSome

@[inline]
def isCtorOverrideSimple? (env : Environment) (declName : Name) : Option CtorOverrideInfo := do
  if let some (.constructor _ info) := getInductiveOverride? env declName then
    return info
  let .ctorInfo val ← env.find? declName | none
  if hasInductiveOverride env val.induct then none
  return {
    induct := val.induct,
    cidx := val.cidx,
    numParams := val.numParams,
    numFields := val.numFields
  }

def isCtorOverride? (declName : Name) : CoreM (Option ConstructorVal) := do
  match getInductiveOverride? (← getEnv) declName with
  | some (.constructor _ { induct, cidx, numParams, numFields }) =>
    let info ← getConstInfo declName
    return some {
      toConstantVal := info.toConstantVal
      induct, cidx, numParams, numFields
      isUnsafe := info.isUnsafe
    }
  | none =>
    let some info ← isCtor? declName | return none
    if hasInductiveOverride (← getEnv) info.induct then
      return none
    return info
  | _ => return none

def getConstInfoCtorOverride (declName : Name) : CoreM ConstructorVal := do
  (← isCtorOverride? declName).getDM (throwError "`{.ofConstName declName}` is not a constructor to the compiler")

def isInductiveOverrideSimpleCore? (env : Environment) (declName : Name) :
    Option InductiveOverrideInfo := do
  match getInductiveOverride? env declName with
  | some (.inductiveType _ info) =>
    return info
  | none =>
    let i ← isInductiveCore? env declName
    return { numParams := i.numParams, ctors := i.ctors, isRec := i.isRec }
  | _ => none

@[inline]
def isInductiveOverride (declName : Name) : CoreM Bool := do
  return (isInductiveOverrideSimpleCore? (← getEnv) declName).isSome

@[inline]
def isInductiveOverrideSimple? (declName : Name) : CoreM (Option InductiveOverrideInfo) := do
  return isInductiveOverrideSimpleCore? (← getEnv) declName

/--
Without overrides, there is a contract that every `opaque` and `def` in the environment with the
name `declName` should fulfill at least one of the following criteria:

1. The definition is a proof or a type former, that is `isProp type` or `isTypeFormerType type`
   is true where `type` is the type of `declName`
2. The definition has computable code, that is, `compileDecl` was run for the declaration
3. `isNoncomputable declName` is true
4. The declaration is tagged `@[implemented_by]`, i.e.
   `(getImplementedBy? (← getEnv) declName).isSome`
5. The declaration is tagged `@[extern]`, i.e. `isExtern (← getEnv) ref`
6. `isCasesOnLike (← getEnv) declName` is true
7. `isNoConfusion (← getEnv) declName` is true
8. `← isProjectionFn declName` is true

With overrides, however, some of the declarations without `isNoncomputable` become noncomputable,
specifically:
1. Constructors of types with overridden runtime representation
2. `casesOn` on types with overridden runtime representation (with the exception of structure
   types, which get special treatmenmt)
3. Projections on types with overridden runtime representation

On the other hand, declarations with an inductive override automatically become computable.
-/
def hasNoncomputableOverride (env : Environment) (declName : Name) : Bool := Id.run do
  let some info := env.findAsync? declName | return false
  match info.kind with
  | .ctor =>
    let .ctorInfo c := info.toConstantInfo | unreachable!
    return hasInductiveOverride env c.induct
  | .defn =>
    -- we let sparse `casesOn`s be computable since we can desugar them to `casesOn`
    if isCasesOnRecursor env declName then
      let type := info.toConstantVal.type
      let indTypeName := casesEliminatorInduct type
      return hasInductiveOverride env indTypeName && !isStructure env indTypeName
    if let some info := env.getProjectionFnInfo? declName then
      let some (.ctorInfo info) := env.find? info.ctorName | return false
      return hasInductiveOverride env info.induct
    return false
  | _ => return false

end Lean.Compiler
