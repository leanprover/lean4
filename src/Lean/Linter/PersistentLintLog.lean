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

/--
A code quality entry recorded into `codeQualityLogExt`, together with the option name of the
linter that produced it. Entries logged via `logCodeQualityEntryIf` carry their linter's option
name, which consumers use to filter by linter selection (e.g. `lake lint --lint-only`); entries
logged via `logCodeQualityEntry` carry `none` and are exempt from such filtering.
-/
structure CodeQualityLogEntry where
  linter? : Option Name
  entry   : CodeQuality.Entry

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

/--
Records the code quality entry `e` into `codeQualityLogExt` so that it is persisted into the
`.olean` and can be recovered by consumers via `getAllCodeQualityEntries`.

This can be safely used in Linters. While regular `Lean.Linter`s, module linters, and stateful
linters all have their environment changes discarded after running, entries they log are
captured per command (see `Command.State.codeQualityEntryTasks`) and merged into the final
environment in `runFrontend`.

The entry is recorded without a linter attribution, so it is recorded unconditionally and no
linter selection flag (e.g. `lake lint --lint-only`) can suppress it. Inside a linter guarded by
an option, use `logCodeQualityEntryIf` instead; this variant is meant for unconditional metrics
not tied to any linter option.
-/
def logCodeQualityEntry [Monad m] [MonadEnv m]
    (e : CodeQuality.Entry) : m Unit :=
  modifyEnv (codeQualityLogExt.addEntry · { linter? := none, entry := e })

/--
Similar to `logLintIf`, but for `logCodeQualityEntry` - i.e. it logs an entry only if the
provided linter option is enabled, taking `linter.all` and linter sets into account. The entry
is recorded with `linterOption.name` as its attribution, so consumers can filter it by linter
selection (e.g. `lake lint --lint-only`).
-/
def logCodeQualityEntryIf [Monad m] [MonadOptions m] [MonadEnv m]
    (linterOption : Lean.Option Bool) (e : CodeQuality.Entry) : m Unit := do
  if getLinterValue linterOption (← getLinterOptions) then
    modifyEnv (codeQualityLogExt.addEntry · { linter? := some linterOption.name, entry := e })

end Lean.Linter
