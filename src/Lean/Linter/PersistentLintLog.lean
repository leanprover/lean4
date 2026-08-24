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

builtin_initialize codeQualityLogExt :
    PersistentEnvExtension CodeQuality.Entry CodeQuality.Entry (Array CodeQuality.Entry) ←
  registerPersistentEnvExtension {
    mkInitial     := pure #[]
    addImportedFn := fun _ => pure #[]
    addEntryFn    := Array.push
    exportEntriesFnEx := fun _ entries =>
      { exported := #[], server := entries, «private» := entries }
  }

def getAllCodeQualityEntries (env : Environment) : Array (Name × Array CodeQuality.Entry) :=
  env.header.moduleNames.mapIdx fun i mod =>
    (mod, codeQualityLogExt.getModuleEntries env i (level := .server))

instance : MonadFileMap (ReaderT FileMap BaseIO) := ⟨read⟩

/--
Records linter warnings and looks up positions of their associated commands from a build
into `lintLogExt` so that consumers (e.g. `lake lint`) can recover them from the `.olean`.
-/
def recordLints (fileMap : FileMap) (env : Environment)
    (commandLints : Array (Option Syntax × MessageLog)) : BaseIO Environment := do
  commandLints.foldlM (init := env) fun env (cmdStx?, messages) => do
    let declRange? : Option DeclarationRange ← match cmdStx? with
      | some stx => (Lean.Elab.getDeclarationRange? stx : ReaderT FileMap _ _).run fileMap
      | none     => pure none
    let position? : Option Position := declRange?.map (·.pos)
    messages.reportedPlusUnreported.foldlM (init := env) fun env m => do
      unless m.data.isLinterMessage do
        return env
      let kind := m.data.kind
      if kind.isAnonymous then
        return env
      let sm ← m.serialize
      return lintLogExt.addEntry env { linter := kind, message := sm, position?, file := m.fileName }

def logCodeQualityEntry [Monad m] [MonadEnv m]
    (e : CodeQuality.Entry) : m Unit :=
  modifyEnv (codeQualityLogExt.addEntry · e)

/--
Similar to `logLintIf`, but for `logCodeQualityEntry` - i.e. it logs an entry only if the
provided linter option is enabled, taking `linter.all` and linter sets into account.
-/
def logCodeQualityEntryIf [Monad m] [MonadOptions m] [MonadEnv m]
    (linterOption : Lean.Option Bool) (e : CodeQuality.Entry) : m Unit := do
  if getLinterValue linterOption (← getLinterOptions) then logCodeQualityEntry e

end Lean.Linter
