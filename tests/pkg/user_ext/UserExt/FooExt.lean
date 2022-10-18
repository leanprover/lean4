import Lean

open Lean

initialize fooExtension : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := NameSet.insert
    addImportedFn := fun es => mkStateFromImportedEntries NameSet.insert {} es
  }

initialize registerTraceClass `myDebug

syntax (name := insertFoo) "insert_foo " ident : command
syntax (name := showFoo) "show_foo_set" : command

open Lean.Elab
open Lean.Elab.Command

@[command_elab insertFoo] def elabInsertFoo : CommandElab := fun stx => do
  trace[myDebug] "testing trace message at insert foo '{stx}'"
  IO.println s!"inserting {stx[1].getId}"
  modifyEnv fun env => fooExtension.addEntry env stx[1].getId

@[command_elab showFoo] def elabShowFoo : CommandElab := fun stx => do
  IO.println s!"foo set: {fooExtension.getState (← getEnv) |>.toList}"
