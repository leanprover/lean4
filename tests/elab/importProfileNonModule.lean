import Lean.Elab.Command

/-!
Tests `profiler.import` (set in `importProfileNonModule.lean.init.sh`) outside the module system:
all data and IR is loaded, and there is no separate public constant map.
-/

open Lean

#eval show CoreM Unit from do
  let some p := (← getEnv).header.importProfile? | throwError "no import profile"
  unless p.setServerEntries?.isNone do throwError "server entries set up"
  for m in (← getEnv).header.modules, c in p.modules do
    unless c.readData?.isSome do throwError "{m.module}: data not read"
    unless c.readIR?.isSome do throwError "{m.module}: IR not read"
    unless c.publicConsts?.isNone do throwError "{m.module}: public constants"
