import Lean.CompactedRegion

open Lean

/-!
Regression test for the `depRegions` argument to `CompactedRegion.save` and
`CompactedRegion.read`.

Saves a standalone olean (`part0`) holding some data, loads it back, then saves a second
olean (`part1`) that *references* the loaded data via the `depRegions` argument. The
compactor should recognize the dep-region object and emit a cross-region pointer rather than
re-serializing it; the reader, given the same dep region, should resolve that pointer via
`fix_object_ptr`'s dep-region lookup.
-/
unsafe def main : IO UInt32 := do
  let part0 : System.FilePath := "./_tmp_dep_regions_0.olean"
  let part1 : System.FilePath := "./_tmp_dep_regions_1.olean"

  -- File 0: standalone payload.
  let payload0 : Array Nat := Array.range 256
  let _ ← CompactedRegion.save part0 `A payload0 #[] none

  let (loaded0, r0) ← CompactedRegion.read (α := Array Nat) part0 #[]
  unless loaded0 = payload0 do
    throw <| IO.userError "file 0 round-trip mismatch"

  -- File 1: payload references `loaded0` (an object from `r0`'s region) and adds its own data.
  let extra : Array Nat := Array.range 32
  let payload1 : Array Nat × Array Nat := (loaded0, extra)
  let _ ← CompactedRegion.save part1 `B payload1 #[r0] none

  -- Loading `part1` without supplying `r0` would either segfault or hit `lean_unreachable`
  -- when `fix_object_ptr` tries to resolve the cross-region pointer; we supply it.
  let (loaded1, _r1) ← CompactedRegion.read (α := Array Nat × Array Nat) part1 #[r0]
  unless loaded1.1 = payload0 do
    throw <| IO.userError "cross-region reference did not round-trip"
  unless loaded1.2 = extra do
    throw <| IO.userError "own-region data did not round-trip"

  IO.FS.removeFile part0
  IO.FS.removeFile part1
  return 0
