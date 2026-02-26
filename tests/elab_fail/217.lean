import Lean
open Lean

#eval show CoreM Unit from do
  (← getEnv).constants.fold _ _
