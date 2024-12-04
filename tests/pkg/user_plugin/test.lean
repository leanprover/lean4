import Lean.LoadDynlib

def main (args : List String) : IO UInt32 := do
  let plugin :: [] := args
    | IO.println "Usage: lean --run test.lean <plugin>"
      return 1
  Lean.loadPlugin plugin
  return 0
