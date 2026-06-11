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
    exportEntriesFn := id
  }

def getAllLints (env : Environment) : Array (Name × Array LintEntry) :=
  env.header.moduleNames.mapIdx fun i mod =>
    (mod, lintLogExt.getModuleEntries env i)

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

end Lean.Linter
