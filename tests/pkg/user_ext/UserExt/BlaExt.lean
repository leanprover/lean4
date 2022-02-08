import Lean

open Lean

initialize blaExtension : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    name          := `blaExt
    addEntryFn    := NameSet.insert
    addImportedFn := fun es => mkStateFromImportedEntries NameSet.insert {} es
  }

syntax (name := insertBla) "insert_bla " ident : command
syntax (name := showBla) "show_bla_set" : command

open Lean.Elab
open Lean.Elab.Command

@[commandElab insertBla] def elabInsertBla : CommandElab := fun stx => do
  IO.println s!"inserting {stx[1].getId}"
  modifyEnv fun env => blaExtension.addEntry env stx[1].getId

@[commandElab showBla] def elabShowBla : CommandElab := fun stx => do
  IO.println s!"bla set: {blaExtension.getState (← getEnv) |>.toList}"
