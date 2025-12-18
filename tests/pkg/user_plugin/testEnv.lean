import UserEnvPlugin
import Lean.LoadDynlib

open Lean

def main (args : List String) : IO UInt32 := do
  let plugin :: [] := args
    | IO.println "Usage: lean --run testEnv.lean <UserEnvPlugin>"
      return 1
  withImporting do
    loadPlugin plugin
    let env ← mkEmptyEnvironment
    IO.println (valExt.getState env)
  return 0
