module

meta import Lean.Elab.Command

/-!
Tests that no import profile is recorded unless `profiler.import` is set.
-/

open Lean

#eval show CoreM Unit from do
  unless (← getEnv).header.importProfile?.isNone do throwError "unexpected import profile"
