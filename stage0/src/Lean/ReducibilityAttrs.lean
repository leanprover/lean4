/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Attributes

namespace Lean

/--
Reducibility status for a definition.
-/
inductive ReducibilityStatus where
  | reducible | semireducible | irreducible
  deriving Inhabited, Repr

/--
Environment extension for storing the reducibility attribute for definitions.
-/
builtin_initialize reducibilityAttrs : EnumAttributes ReducibilityStatus ←
  registerEnumAttributes
    [(`reducible, "reducible", ReducibilityStatus.reducible),
     (`semireducible, "semireducible", ReducibilityStatus.semireducible),
     (`irreducible, "irreducible", ReducibilityStatus.irreducible)]

@[export lean_get_reducibility_status]
private def getReducibilityStatusImp (env : Environment) (declName : Name) : ReducibilityStatus :=
  match reducibilityAttrs.getValue env declName with
  | some s => s
  | none   => ReducibilityStatus.semireducible

@[export lean_set_reducibility_status]
private def setReducibilityStatusImp (env : Environment) (declName : Name) (s : ReducibilityStatus) : Environment :=
  match reducibilityAttrs.setValue env declName s with
  | Except.ok env => env
  | _ => env -- TODO(Leo): we should extend EnumAttributes.setValue in the future and ensure it never fails

/-- Return the reducibility attribute for the given declaration. -/
def getReducibilityStatus [Monad m] [MonadEnv m] (declName : Name) : m ReducibilityStatus := do
  return getReducibilityStatusImp (← getEnv) declName

/-- Set the reducibility attribute for the given declaration. -/
def setReducibilityStatus [Monad m] [MonadEnv m] (declName : Name) (s : ReducibilityStatus) : m Unit := do
  modifyEnv fun env => setReducibilityStatusImp env declName s

/-- Set the given declaration as `[reducible]` -/
def setReducibleAttribute [Monad m] [MonadEnv m] (declName : Name) : m Unit := do
  setReducibilityStatus declName ReducibilityStatus.reducible

/-- Return `true` if the given declaration has been marked as `[reducible]`. -/
def isReducible [Monad m] [MonadEnv m] (declName : Name) : m Bool := do
  match (← getReducibilityStatus declName) with
  | ReducibilityStatus.reducible => return true
  | _ => return false

/-- Return `true` if the given declaration has been marked as `[irreducible]` -/
def isIrreducible [Monad m] [MonadEnv m] (declName : Name) : m Bool := do
  match (← getReducibilityStatus declName) with
  | ReducibilityStatus.irreducible => return true
  | _ => return false

end Lean
