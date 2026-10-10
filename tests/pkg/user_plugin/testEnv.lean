import UserEnvPlugin
import Lean.LoadDynlib

open Lean

@[noinline]
def withPlugin : IO Unit := do
  let env ← mkEmptyEnvironment
  IO.println (valExt.getState env)

def main (args : List String) : IO UInt32 := do
  let plugin :: [] := args
    | IO.println "Usage: lean --run testEnv.lean <UserEnvPlugin>"
      return 1
  withImporting do
    loadPlugin plugin
    -- the bytecode interpreter loads all symbols
    -- at the beginning of the function but we need
    -- to make sure `valExt` is loaded after `loadPlugin`
    -- so we need to put it into a separate function
    withPlugin
  return 0
