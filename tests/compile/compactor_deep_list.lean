import Lean.CompactedRegion

open Lean

/-!
Regression test that `CompactedRegion.save` can compact a deep constructor chain without
exhausting the native call stack. The long `List Nat` forces the object compactor to walk through
many nested cons cells before writing the file.
-/

def depth : Nat := 20000

def mkDeepList (n : Nat) : List Nat := Id.run do
  let mut xs := []
  for i in [0:n] do
    xs := i :: xs
  return xs

unsafe def main : IO UInt32 := do
  let tmpFile : System.FilePath := "./_tmp_compactor_deep_list.olean"
  let xs := mkDeepList depth
  let _ ← CompactedRegion.save tmpFile `CompactorDeepList xs #[] none
  let (ys, _region) ← CompactedRegion.read (α := List Nat) tmpFile #[]
  unless ys.length == depth do
    throw <| IO.userError s!"round-trip length mismatch: expected {depth}, got {ys.length}"
  unless ys.head? == some (depth - 1) do
    throw <| IO.userError "round-trip head mismatch"
  IO.FS.removeFile tmpFile
  return 0
