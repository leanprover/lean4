module

public import Lean.CompactedRegion

/-!
Tests compact-region serialization of the escape objects used by nested `NOption` values and the
largest immediate `Nat`.
-/

open Lean

public unsafe def main : IO Unit := do
  let path : System.FilePath := "./_tmp_noption.olean"
  let maxSmallNat : Nat := 2 ^ (System.Platform.numBits - 1) - 1
  let value : NOption (NOption Nat) := .some (.some maxSmallNat)
  let _ ← CompactedRegion.save path `NOption value #[] none
  let (loaded, _region) ← CompactedRegion.read (α := NOption (NOption Nat)) path #[]
  IO.FS.removeFile path
  match loaded with
  | .some (.some n) =>
    unless n == maxSmallNat do
      throw <| IO.userError "compact-region roundtrip changed the payload"
  | _ => throw <| IO.userError "compact-region roundtrip changed the constructors"
  IO.println "ok"
