import Lean.CompactedRegion

open Lean

/-!
Tests `CompactedRegion.save`/`read` with `allowClosures := true`: closures (with captured data)
are serialized in the `v3` olean format and round-trip within the same process.
-/
unsafe def main : IO Unit := do
  let tmpFile : System.FilePath := "./_compact_closure_test.olean"

  -- Simple closure with captured string
  let captured := "hello"
  let f : Nat → String := fun n => s!"{captured} {n}"
  let _ ← CompactedRegion.save tmpFile `test f #[] none true
  let (g, _region) ← CompactedRegion.read (α := Nat → String) tmpFile #[]
  IO.println (g 42)
  IO.println (g 0)

  -- Closure capturing an array
  let xs := #[10, 20, 30]
  let h : Nat → Nat := fun i => xs.foldl (· + ·) i
  let _ ← CompactedRegion.save tmpFile `test2 h #[] none true
  let (h', _region2) ← CompactedRegion.read (α := Nat → Nat) tmpFile #[]
  IO.println (toString (h' 1))
  IO.println (toString (h' 100))

  IO.FS.removeFile tmpFile
