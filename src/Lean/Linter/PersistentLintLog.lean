/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Lean.Environment
public import Lean.Message
public import Lean.Linter.Init
public import Lean.Linter.CodeQuality.Basic
public import Lean.Elab.DeclarationRange

public section

namespace Lean.Linter

structure LintEntry where
  linter  : Name
  message : SerialMessage
  position? : Option Position := none
  file : String

builtin_initialize lintLogExt :
    PersistentEnvExtension LintEntry LintEntry (Array LintEntry) ←
  registerPersistentEnvExtension {
    mkInitial     := pure #[]
    addImportedFn := fun _ => pure #[]
    addEntryFn    := Array.push
    exportEntriesFnEx := fun _ entries =>
      { exported := #[], server := entries, «private» := entries }
  }

def getAllLints (env : Environment) : Array (Name × Array LintEntry) :=
  env.header.moduleNames.mapIdx fun i mod =>
    (mod, lintLogExt.getModuleEntries env i (level := .server))

/-- A code quality entry recorded by `Lean.Linter.recordLints`, together with the option name of
the linter that logged it (the tag attached by `Lean.Linter.logCodeQualityEntry`). -/
structure CodeQualityLogEntry where
  linter : Name
  entry  : CodeQuality.Entry

builtin_initialize codeQualityLogExt :
    PersistentEnvExtension CodeQualityLogEntry CodeQualityLogEntry (Array CodeQualityLogEntry) ←
  registerPersistentEnvExtension {
    mkInitial     := pure #[]
    addImportedFn := fun _ => pure #[]
    addEntryFn    := Array.push
    exportEntriesFnEx := fun _ entries =>
      { exported := #[], server := entries, «private» := entries }
  }

def getAllCodeQualityEntries (env : Environment) : Array (Name × Array CodeQualityLogEntry) :=
  env.header.moduleNames.mapIdx fun i mod =>
    (mod, codeQualityLogExt.getModuleEntries env i (level := .server))

instance : MonadFileMap (ReaderT FileMap BaseIO) := ⟨read⟩

/--
Records linter warnings and looks up positions of their associated commands from a build
into `lintLogExt` so that consumers (e.g. `lake lint`) can recover them from the `.olean`.
Messages carrying code quality entries (see `Lean.Linter.logCodeQualityEntry`) are recorded
into `codeQualityLogExt` instead, keyed by the producing linter's option name, without any
position information.
-/
def recordLints (fileMap : FileMap) (env : Environment)
    (commandLints : Array (Option Syntax × MessageLog)) : BaseIO Environment := do
  commandLints.foldlM (init := env) fun env (cmdStx?, messages) => do
    let declRange? : Option DeclarationRange ← match cmdStx? with
      | some stx => (Lean.Elab.getDeclarationRange? stx : ReaderT FileMap _ _).run fileMap
      | none     => pure none
    let position? : Option Position := declRange?.map (·.pos)
    messages.reportedPlusUnreported.foldlM (init := env) fun env m => do
      let kind := m.data.kind
      if let some entry := m.data.codeQualityEntry? then
        -- Without a linter-name tag, `kind` is anonymous (or falls through to the marker tag);
        -- such entries cannot be attributed to a linter and are dropped.
        if kind.isAnonymous || kind == codeQualityMessageTag then
          return env
        return codeQualityLogExt.addEntry env { linter := kind, entry }
      unless m.data.isLinterMessage do
        return env
      if kind.isAnonymous then
        return env
      let sm ← m.serialize
      return lintLogExt.addEntry env { linter := kind, message := sm, position?, file := m.fileName }

end Lean.Linter
