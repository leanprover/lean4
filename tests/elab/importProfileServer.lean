module

meta import Lean.Elab.Command

/-!
Tests `profiler.import` (set in `importProfileServer.lean.init.sh`) when importing at the language
server's level: server entries are set up, and IR is loaded for every module.
-/

open Lean

#eval show CoreM Unit from do
  unless Elab.inServer.get (← getOptions) do throwError "test must run in server mode"
  let some p := (← getEnv).header.importProfile? | throwError "no import profile"
  unless p.setServerEntries?.isSome do throwError "server entries not set up"
  for m in (← getEnv).header.modules, c in p.modules do
    unless c.readIR?.isSome do throwError "{m.module}: IR not read"
