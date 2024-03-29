import Lean.Util.Profiler

open Lean

def main (args : List String) : IO Unit := do
  let profiles ← args.toArray.mapM fun path => do
    let json ← IO.FS.readFile ⟨path⟩
    let profile ← IO.ofExcept $ Json.parse json
    IO.ofExcept <| fromJson? profile
  let profile := Firefox.Profile.collide profiles
  IO.println <| Json.compress <| toJson profile
