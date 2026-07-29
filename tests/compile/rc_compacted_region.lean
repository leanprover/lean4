import Lean.CompactedRegion

open Lean

/-!
Tests `RcCompactedRegion.read`/`map`: compacted data saved with `CompactedRegion.save` round-trips
within the same process, and `map` deep-copies its result, so region-resident data returned from
`map` remains valid after the last reference to the region is dropped and the region is freed.
-/
unsafe def main : IO Unit := do
  let tmpFile : System.FilePath := "./_tmp_rc_compacted_region.olean"

  -- pair payload with a compacted string
  let payload := ("hello", 42)
  discard <| CompactedRegion.save tmpFile `test payload #[] none

  let region ← RcCompactedRegion.read (String × Nat) tmpFile
  IO.println (← region.map fun (s, n) => s!"{s} {n}")
  IO.println (← region.map fun (s, _) => s!"{s} 0")
  -- returns the region data, forcing `map` to copy it
  let escaped ← region.map id
  -- last reference to the region is gone (inspect IR to confirm)
  -- copied data must remain valid
  IO.println escaped
