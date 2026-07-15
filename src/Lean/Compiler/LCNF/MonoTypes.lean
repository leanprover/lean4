/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.LCNF.Util
public import Lean.Compiler.LCNF.BaseTypes
public import Lean.Compiler.LCNF.Irrelevant

public section

namespace Lean.Compiler.LCNF

private builtin_initialize trivialStructureInfoExt : MapDeclarationExtension (Option TrivialStructureInfo) ←
  mkMapDeclarationExtension (asyncMode := .sync)

/-- Eagerly computes and persists the trivial-structure info of `declName`; see `compileDecls`. -/
def setHasTrivialStructure? (declName : Name) : CoreM Unit :=
  Irrelevant.setHasTrivialStructure? trivialStructureInfoExt
    (fun type => Meta.isProp type <||> Meta.isTypeFormerType type) declName

/--
Return `some fieldIdx` if `declName` is the name of an inductive datatype s.t.
- It does not have builtin support in the runtime.
- It has only one constructor.
- This constructor has only one computationally relevant field.

Requires `compileDecls` to have been run for inductive `declName`.
-/
def hasTrivialStructure? (declName : Name) : CoreM (Option TrivialStructureInfo) :=
  Irrelevant.hasTrivialStructure? trivialStructureInfoExt declName

def getParamTypes (type : Expr) : Array Expr :=
  go type #[]
where
  go (type : Expr) (r : Array Expr) :=
    match type with
    | .forallE _ d b _ => go b (r.push d)
    | _ => r

/--
Convert a LCNF type from the base phase to the mono phase.

LCNF types in the mono phase do not have dependencies,
and universe levels have been erased.

The type contains only `→` and constants.
-/
partial def toMonoType (type : Expr) : CoreM Expr := do
  let type := type.headBeta
  match type with
  | .const .. => visitApp type #[]
  | .app .. => type.withApp visitApp
  | .forallE n d b bi =>
    let monoB ← toMonoType (b.instantiate1 anyExpr)
    match monoB with
    | .const ``lcErased _ => return erasedExpr
    | _ =>
      -- preserve parameter names for readability and to avoid recompilation from signature changes
      return .forallE n (← toMonoType d) monoB bi
  | .sort _ => return erasedExpr
  | .mdata d b => return .mdata d (← toMonoType b)
  | _ => return anyExpr
where
  visitApp (f : Expr) (args : Array Expr) : CoreM Expr := do
    match f with
    | .const ``lcErased _ => return erasedExpr
    | .const ``lcAny _ => return anyExpr
    | .const ``Decidable _ => return mkConst ``Bool
    | .const declName us =>
      if let some info ← hasTrivialStructure? declName then
        let ctorType ← getOtherDeclBaseType info.ctorName []
        toMonoType (getParamTypes (← instantiateForall ctorType args[*...info.numParams]))[info.fieldIdx]!
      else
        let mut result := mkConst declName
        let mut type ← getOtherDeclBaseType declName us
        if type.isErased then return erasedExpr
        for arg in args do
          let .forallE _ d b _ := type.headBeta | unreachable!
          let arg := arg.headBeta
          if d matches .const ``lcErased _ | .sort _ then
            result := mkApp result (← toMonoType arg)
          else
            result := mkApp result anyExpr
          type := b.instantiate1 arg
        return result
    | _ => return anyExpr

/--
State for the environment extension used to save the LCNF mono phase type for declarations
that do not have code associated with them.
Example: constructors, inductive types, foreign functions.
-/
builtin_initialize monoTypeExt : MapDeclarationExtension Expr ←
  mkMapDeclarationExtension (asyncMode := .sync)

/-- Eagerly computes and persists the mono type of `declName`; see `compileDecls`. -/
def setOtherDeclMonoType (declName : Name) : CoreM Unit := do
  unless (monoTypeExt.find? (← getEnv) declName).isSome do
    modifyEnv (monoTypeExt.insert · declName (← toMonoType (← getOtherDeclBaseType declName [])))

/--
Returns the LCNF mono-phase type of `declName`, a declaration without associated code (constructor,
inductive type, foreign function, or `noncomputable` definition).

Inductive types and their constructors are compiled eagerly by `compileInductives` (their mono type
can depend on private constructor field types and so must be precomputed in the defining module); a
miss for those is reported as an error. Other declarations have their mono type computed from the
signature on demand and cached for the current module.
-/
def getOtherDeclMonoType (declName : Name) : CoreM Expr := do
  if let some type := monoTypeExt.find? (← getEnv) declName then
    return type
  if (← getEnv).find? declName matches some (.inductInfo _) | some (.ctorInfo _) then
    throwError "`{declName}` was not compiled; `compileDecls` must run on inductive types first"
  let type ← toMonoType (← getOtherDeclBaseType declName [])
  -- avoid `addEntry` for local-only caching
  modifyEnv (monoTypeExt.modifyState · (monoTypeExt.addEntryFn · (declName, type)))
  return type

end Lean.Compiler.LCNF
