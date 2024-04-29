/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Attributes
import Lean.ScopedEnvExtension

namespace Lean

/--
Reducibility status for a definition.
-/
inductive ReducibilityStatus where
  | reducible | semireducible | irreducible
  deriving Inhabited, Repr

builtin_initialize reducibilityCoreExt : PersistentEnvExtension (Name × ReducibilityStatus) (Name × ReducibilityStatus) (NameMap ReducibilityStatus) ←
  registerPersistentEnvExtension {
    name            := `reducibilityCore
    mkInitial       := pure {}
    addImportedFn   := fun _ _ => pure {}
    addEntryFn      := fun (s : NameMap ReducibilityStatus) (p : Name × ReducibilityStatus) => s.insert p.1 p.2
    exportEntriesFn := fun m =>
      let r : Array (Name × ReducibilityStatus) := m.fold (fun a n p => a.push (n, p)) #[]
      r.qsort (fun a b => Name.quickLt a.1 b.1)
    statsFn         := fun s => "reducibility attribute core extension" ++ Format.line ++ "number of local entries: " ++ format s.size
  }

builtin_initialize reducibilityExtraExt : SimpleScopedEnvExtension (Name × ReducibilityStatus) (SMap Name ReducibilityStatus) ←
  registerSimpleScopedEnvExtension {
    name := `reducibilityExtra
    initial := {}
    addEntry := fun d (declName, status) => d.insert declName status
    finalizeImport := fun d => d.switch
  }

@[export lean_get_reducibility_status]
def getReducibilityStatusCore (env : Environment) (declName : Name) : ReducibilityStatus :=
  let m := reducibilityExtraExt.getState env
  if let some status := m.find? declName then
    status
  else match env.getModuleIdxFor? declName with
  | some modIdx =>
    match (reducibilityCoreExt.getModuleEntries env modIdx).binSearch (declName, .semireducible) (fun a b => Name.quickLt a.1 b.1) with
    | some (_, status) => status
    | none => .semireducible
  | none => (reducibilityCoreExt.getState env).find? declName |>.getD .semireducible

def setReducibilityStatusCore (env : Environment) (declName : Name) (status : ReducibilityStatus) (attrKind : AttributeKind) (currNamespace : Name) : Environment :=
  if attrKind matches .global then
    match env.getModuleIdxFor? declName with
    | some _ =>
      -- Trying to set the attribute of a declaration defined in an imported module.
      reducibilityExtraExt.addEntry env (declName, status)
    | none =>
      --
      reducibilityCoreExt.addEntry env (declName, status)
  else
    -- `scoped` and `local` must be handled by `reducibilityExtraExt`
    reducibilityExtraExt.addCore env (declName, status) attrKind currNamespace

@[export lean_set_reducibility_status]
private def setReducibilityStatusImp (env : Environment) (declName : Name) (status : ReducibilityStatus) : Environment :=
  setReducibilityStatusCore env declName status .global .anonymous

builtin_initialize
  registerBuiltinAttribute {
    ref             := by exact decl_name%
    name            := `irreducible
    descr           := "irreducible declaration"
    add             := fun declName stx attrKind => do
      Attribute.Builtin.ensureNoArgs stx
      let ns ← getCurrNamespace
      modifyEnv fun env => setReducibilityStatusCore env declName .irreducible attrKind ns
    applicationTime := .afterTypeChecking
 }

builtin_initialize
  registerBuiltinAttribute {
    ref             := by exact decl_name%
    name            := `reducible
    descr           := "reducible declaration"
    add             := fun declName stx attrKind => do
      Attribute.Builtin.ensureNoArgs stx
      let ns ← getCurrNamespace
      modifyEnv fun env => setReducibilityStatusCore env declName .reducible attrKind ns
    applicationTime := .afterTypeChecking
 }

builtin_initialize
  registerBuiltinAttribute {
    ref             := by exact decl_name%
    name            := `semireducible
    descr           := "semireducible declaration"
    add             := fun declName stx attrKind => do
      Attribute.Builtin.ensureNoArgs stx
      let ns ← getCurrNamespace
      modifyEnv fun env => setReducibilityStatusCore env declName .reducible attrKind ns
    applicationTime := .afterTypeChecking
 }

/-- Return the reducibility attribute for the given declaration. -/
def getReducibilityStatus [Monad m] [MonadEnv m] (declName : Name) : m ReducibilityStatus := do
  return getReducibilityStatusCore (← getEnv) declName

/-- Set the reducibility attribute for the given declaration. -/
def setReducibilityStatus [Monad m] [MonadEnv m] (declName : Name) (s : ReducibilityStatus) : m Unit := do
  modifyEnv fun env => setReducibilityStatusCore env declName s .global .anonymous

/-- Set the given declaration as `[reducible]` -/
def setReducibleAttribute [Monad m] [MonadEnv m] (declName : Name) : m Unit := do
  setReducibilityStatus declName ReducibilityStatus.reducible

/-- Return `true` if the given declaration has been marked as `[reducible]`. -/
def isReducible [Monad m] [MonadEnv m] (declName : Name) : m Bool := do
  match (← getReducibilityStatus declName) with
  | .reducible => return true
  | _ => return false

/-- Return `true` if the given declaration has been marked as `[irreducible]` -/
def isIrreducible [Monad m] [MonadEnv m] (declName : Name) : m Bool := do
  match (← getReducibilityStatus declName) with
  | .irreducible => return true
  | _ => return false

end Lean
