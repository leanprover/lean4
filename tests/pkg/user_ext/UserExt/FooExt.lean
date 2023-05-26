import Lean

open Lean

initialize fooFloat : Float ← pure 1.2
initialize foo8 : UInt8 ← pure 12
initialize foo16 : UInt16 ← pure 1234
initialize foo32 : UInt32 ← pure 1234
initialize foo64 : UInt64 ← pure 1234
initialize fooNat : Nat ← pure 1234
initialize fooProd : UInt32 × Bool ← pure (1234, true)

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

@[command_elab showFoo] def elabShowFoo : CommandElab := fun _ => do
  IO.println s!"foo set: {fooExtension.getState (← getEnv) |>.toArray |>.qsort Name.lt}"
