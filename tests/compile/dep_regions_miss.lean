import Lean.CompactedRegion

open Lean

/-!
Regression test for the dep-aware fast-path skip in `compacted_region::read()`.

Saves two distinct payloads to two different files with the same `mod` `Name`, so both files
derive the same saved `base_addr`. Loading the first mmaps successfully at that address;
loading the second finds the address occupied and falls back to `malloc`+`read` —
`m_begin ≠ m_base_addr`. We then save a third file whose data references the malloc'd
payload via `depRegions := #[r_B]`, and load it back.

When the dependent file (which itself mmaps at a different `base_addr`) reaches
`compacted_region::read()`, the fast path must check **all** dep regions for
`m_begin == m_base_addr` and fall through to the full pointer-fixup walk if any didn't land
at their saved address. If the fast path only checks `m_begin == m_base_addr` for the
current region (master's behavior before this fix), the cross-region pointer still holds
the dep's saved address — which in this process happens to be mapped, but mapped to a
*different file's data* (the first load's). The test catches that by asserting the loaded
data matches `payload_b`, not `payload_a`.
-/
unsafe def main : IO UInt32 := do
  let part_a : System.FilePath := "./_tmp_dep_regions_miss_a.olean"
  let part_b : System.FilePath := "./_tmp_dep_regions_miss_b.olean"
  let part_c : System.FilePath := "./_tmp_dep_regions_miss_c.olean"

  let payload_a : Array Nat := (Array.range 256).map (· + 1000)
  let payload_b : Array Nat := (Array.range 256).map (· + 9000)
  let _ ← CompactedRegion.save part_a `Same payload_a #[] none
  let _ ← CompactedRegion.save part_b `Same payload_b #[] none

  -- First load: mmap succeeds at the saved `base_addr` derived from `Same`.
  let (_, _r_a) ← CompactedRegion.read (α := Array Nat) part_a #[]
  -- Second load: same `mod` → same saved `base_addr`, but it's already occupied by `_r_a`,
  -- so mmap fails and the reader falls back to malloc. `m_begin ≠ m_base_addr`.
  let (loaded_b, r_b) ← CompactedRegion.read (α := Array Nat) part_b #[]
  unless loaded_b = payload_b do
    throw <| IO.userError "malloc-fallback load did not round-trip identically"

  -- Save part_c referencing the malloc-loaded `loaded_b`. The compactor recognizes
  -- objects in `r_b`'s range and emits a cross-region pointer using `r_b`'s saved
  -- `base_addr` (which equals `r_a`'s saved `base_addr`).
  let extra : Array Nat := Array.range 32
  let payload_c : Array Nat × Array Nat := (loaded_b, extra)
  let _ ← CompactedRegion.save part_c `Other payload_c #[r_b] none

  -- Load part_c. Its own region mmaps at a different `base_addr` (mod `Other`), so the
  -- own-region check passes — but `r_b` has `m_begin ≠ m_base_addr`, so the fast path must
  -- fall through to the full walk to translate the cross-region pointer to `r_b`'s
  -- malloc'd memory. If the walk is skipped, the unfixed pointer instead reads into
  -- `_r_a`'s mmap (which holds `payload_a`, not `payload_b`).
  let (loaded_c, _r_c) ← CompactedRegion.read (α := Array Nat × Array Nat) part_c #[r_b]
  unless loaded_c.1 = payload_b do
    throw <| IO.userError "fast path skipped fixup: cross-region pointer resolved to wrong dep"
  unless loaded_c.2 = extra do
    throw <| IO.userError "own-region data didn't round-trip"

  IO.FS.removeFile part_a
  IO.FS.removeFile part_b
  IO.FS.removeFile part_c
  return 0
