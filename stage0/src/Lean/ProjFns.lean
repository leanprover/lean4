/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Environment

namespace Lean

/- Given a structure `S`, Lean automatically creates an auxiliary definition (projection function)
   for each field. This structure caches information about these auxiliary definitions. -/
structure ProjectionFunctionInfo :=
  (ctorName : Name)  -- Constructor associated with the auxiliary projection function.
  (nparams : Nat)    -- Number of parameters in the structure
  (i : Nat)          -- The field index associated with the auxiliary projection function.
  (fromClass : Bool) -- `true` if the structure is a class

@[export lean_mk_projection_info]
def mkProjectionInfoEx (ctorName : Name) (nparams : Nat) (i : Nat) (fromClass : Bool) : ProjectionFunctionInfo :=
  {ctorName := ctorName, nparams := nparams, i := i, fromClass := fromClass }
@[export lean_projection_info_from_class]
  def ProjectionFunctionInfo.fromClassEx (info : ProjectionFunctionInfo) : Bool := info.fromClass

instance : Inhabited ProjectionFunctionInfo :=
  ⟨{ ctorName := arbitrary _, nparams := arbitrary _, i := 0, fromClass := false }⟩

builtin_initialize projectionFnInfoExt : SimplePersistentEnvExtension (Name × ProjectionFunctionInfo) (NameMap ProjectionFunctionInfo) ←
  registerSimplePersistentEnvExtension {
    name          := `projinfo,
    addImportedFn := fun as => {},
    addEntryFn    := fun s p => s.insert p.1 p.2,
    toArrayFn     := fun es => es.toArray.qsort (fun a b => Name.quickLt a.1 b.1)
  }

@[export lean_add_projection_info]
def addProjectionFnInfo (env : Environment) (projName : Name) (ctorName : Name) (nparams : Nat) (i : Nat) (fromClass : Bool) : Environment :=
  projectionFnInfoExt.addEntry env (projName, { ctorName := ctorName, nparams := nparams, i := i, fromClass := fromClass })

namespace Environment

@[export lean_get_projection_info]
def getProjectionFnInfo? (env : Environment) (projName : Name) : Option ProjectionFunctionInfo :=
  match env.getModuleIdxFor? projName with
  | some modIdx =>
    match (projectionFnInfoExt.getModuleEntries env modIdx).binSearch (projName, arbitrary _) (fun a b => Name.quickLt a.1 b.1) with
    | some e => some e.2
    | none   => none
  | none        => (projectionFnInfoExt.getState env).find? projName

def isProjectionFn (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some modIdx => (projectionFnInfoExt.getModuleEntries env modIdx).binSearchContains (n, arbitrary _) (fun a b => Name.quickLt a.1 b.1)
  | none        => (projectionFnInfoExt.getState env).contains n

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
