import Lean.Util.Profiler

/-!

Usage:
```sh
lean --run ./script/collideProfiles.lean **/*.lean.json ... > merged.json
```

Merges multiple `trace.profiler.output` profiles into a single one while deduplicating samples with
the same stack. This is useful for building cumulative profiles of medium-to-large projects because
Firefox Profiler cannot handle hundreds of tracks and the deduplication will also ensure that the
profile is small enough for uploading.

As ordering of samples is not meaningful after this transformation, only "Call Tree" and "Flame
Graph" are useful for such profiles.
-/

open Lean

def main (args : List String) : IO Unit := do
  let profiles ← args.toArray.mapM fun path => do
    let json ← IO.FS.readFile ⟨path⟩
    let profile ← IO.ofExcept $ Json.parse json
    IO.ofExcept <| fromJson? profile
  -- NOTE: `collide` should not be interpreted
  let profile := Firefox.Profile.collide profiles
  IO.println <| Json.compress <| toJson profile
