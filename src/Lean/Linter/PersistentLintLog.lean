/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Lean.Environment
public import Lean.Message

public section

namespace Lean.Linter

structure LintEntry where
  linter  : Name
  message : SerialMessage

builtin_initialize lintLogExt :
    PersistentEnvExtension LintEntry LintEntry (Array LintEntry) ←
  registerPersistentEnvExtension {
    mkInitial     := pure #[]
    addImportedFn := fun _ => pure #[]
    addEntryFn    := Array.push
    exportEntriesFn := id
  }

def getAllLints (env : Environment) : Array (Name × Array LintEntry) :=
  env.header.moduleNames.mapIdx fun i mod =>
    (mod, lintLogExt.getModuleEntries env i)

def recordLints (env : Environment) (messages : MessageLog) : BaseIO Environment := do
  messages.reportedPlusUnreported.foldlM (init := env) fun env m => do
    let kind := m.data.kind
    if kind.isAnonymous then
      return env
    let sm ← m.serialize
    return lintLogExt.addEntry env { linter := kind, message := sm }

end Lean.Linter
