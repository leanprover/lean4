/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.EnvExtension

namespace Lean

/--
Given a structure `S`, Lean automatically creates an auxiliary definition (projection function)
for each field. This structure caches information about these auxiliary definitions.
-/
structure ProjectionFunctionInfo where
  /-- Constructor associated with the auxiliary projection function. -/
  ctorName : Name
  /-- Number of parameters in the structure -/
  numParams : Nat
  /-- The field index associated with the auxiliary projection function. -/
  i : Nat
  /-- `true` if the structure is a class. -/
  fromClass : Bool
  deriving Inhabited, Repr

@[export lean_mk_projection_info]
def mkProjectionInfoEx (ctorName : Name) (numParams : Nat) (i : Nat) (fromClass : Bool) : ProjectionFunctionInfo :=
  { ctorName, numParams, i, fromClass }
@[export lean_projection_info_from_class]
def ProjectionFunctionInfo.fromClassEx (info : ProjectionFunctionInfo) : Bool :=
  info.fromClass

builtin_initialize projectionFnInfoExt : MapDeclarationExtension ProjectionFunctionInfo ← mkMapDeclarationExtension

@[export lean_add_projection_info]
def addProjectionFnInfo (env : Environment) (projName : Name) (ctorName : Name) (numParams : Nat) (i : Nat) (fromClass : Bool) : Environment :=
  projectionFnInfoExt.insert env projName { ctorName, numParams, i, fromClass }

namespace Environment

@[export lean_get_projection_info]
def getProjectionFnInfo? (env : Environment) (projName : Name) : Option ProjectionFunctionInfo :=
  projectionFnInfoExt.find? env projName

def isProjectionFn (env : Environment) (declName : Name) : Bool :=
  projectionFnInfoExt.contains env declName

/-- If `projName` is the name of a projection function, return the associated structure name -/
def getProjectionStructureName? (env : Environment) (projName : Name) : Option Name :=
  match env.getProjectionFnInfo? projName with
  | none          => none
  | some projInfo =>
    match env.find? projInfo.ctorName with
    | some (ConstantInfo.ctorInfo val) => some val.induct
    | _ => none

end Environment

def isProjectionFn [MonadEnv m] [Monad m] (declName : Name) : m Bool :=
  return (← getEnv).isProjectionFn declName

def getProjectionFnInfo? [MonadEnv m] [Monad m] (declName : Name) : m (Option ProjectionFunctionInfo) :=
  return (← getEnv).getProjectionFnInfo? declName

end Lean
