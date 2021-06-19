/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Attributes

namespace Lean

inductive ReducibilityStatus where
  | reducible | semireducible | irreducible
  deriving Inhabited, Repr

builtin_initialize reducibilityAttrs : EnumAttributes ReducibilityStatus ←
  registerEnumAttributes `reducibility
    [(`reducible, "reducible", ReducibilityStatus.reducible),
     (`semireducible, "semireducible", ReducibilityStatus.semireducible),
     (`irreducible, "irreducible", ReducibilityStatus.irreducible)]

@[export lean_get_reducibility_status]
def getReducibilityStatusImp (env : Environment) (declName : Name) : ReducibilityStatus :=
  match reducibilityAttrs.getValue env declName with
  | some s => s
  | none   => ReducibilityStatus.semireducible

@[export lean_set_reducibility_status]
def setReducibilityStatusImp (env : Environment) (declName : Name) (s : ReducibilityStatus) : Environment :=
  match reducibilityAttrs.setValue env declName s with
  | Except.ok env => env
  | _ => env -- TODO(Leo): we should extend EnumAttributes.setValue in the future and ensure it never fails

def getReducibilityStatus {m} [Monad m] [MonadEnv m] (declName : Name) : m ReducibilityStatus := do
  return getReducibilityStatusImp (← getEnv) declName

def setReducibilityStatus {m} [Monad m] [MonadEnv m] (declName : Name) (s : ReducibilityStatus) : m Unit := do
  modifyEnv fun env => setReducibilityStatusImp env declName s

def setReducibleAttribute {m} [Monad m] [MonadEnv m] (declName : Name) : m Unit := do
  setReducibilityStatus declName ReducibilityStatus.reducible

def isReducible {m} [Monad m] [MonadEnv m] (declName : Name) : m Bool := do
  match (← getReducibilityStatus declName) with
  | ReducibilityStatus.reducible => true
  | _ => false

end Lean
