import Lean.CompactedRegion

open Lean

/-!
Regression test for `CompactedRegion.save` / `CompactedRegion.read` chained-`Compactor`
object sharing.

Saves three parts where parts 1 and 2 both reference the same `Array Nat`. The chained
`Compactor` should emit that array's bytes exactly once (in part 1), with part 2 holding only
a cross-region reference. We verify both halves:

* **dedup:** part 2's file size should be substantially smaller than part 1's, since part 2
  doesn't re-serialize the shared array.
* **round-trip:** loading via `CompactedRegion.read` with the prior regions as `depRegions`
  reproduces the original arrays, exercising `fix_object_ptr`'s dep-region lookup.
-/
unsafe def main : IO UInt32 := do
  let part0 : System.FilePath := "./_tmp_compactor_chain_0.olean"
  let part1 : System.FilePath := "./_tmp_compactor_chain_1.olean"
  let part2 : System.FilePath := "./_tmp_compactor_chain_2.olean"

  let shared : Array Nat := Array.range 256
  let cs ← CompactedRegion.save part0 `Test (0 : Nat) #[] none
  let cs ← CompactedRegion.save part1 `Test shared    #[] (some cs)
  let _  ← CompactedRegion.save part2 `Test shared    #[] (some cs)

  let s1 := (← IO.FS.readBinFile part1).size
  let s2 := (← IO.FS.readBinFile part2).size
  -- Part 2 should be much smaller than part 1: the chained compactor sees the shared array
  -- was already emitted to part 1 and writes only a cross-region pointer. A factor of 4 is
  -- generous — in practice part 2 is dominated by the olean header + a single root pointer.
  unless 4 * s2 < s1 do
    throw <| IO.userError s!"dedup did not take effect: part1={s1}, part2={s2}"

  let (_,  r0) ← CompactedRegion.read (α := Nat)       part0 #[]
  let (a1, r1) ← CompactedRegion.read (α := Array Nat) part1 #[r0]
  let (a2, _ ) ← CompactedRegion.read (α := Array Nat) part2 #[r0, r1]
  unless a1 = shared do
    throw <| IO.userError "part 1 round-trip mismatch"
  unless a2 = shared do
    throw <| IO.userError "part 2 round-trip mismatch"

  IO.FS.removeFile part0
  IO.FS.removeFile part1
  IO.FS.removeFile part2
  return 0
