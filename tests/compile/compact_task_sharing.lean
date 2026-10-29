import Lean.CompactedRegion

open Lean

/-!
Tests that `CompactedRegion.save` max-shares a `Task.pure` with a finished spawned task that holds
the same value. The runtime marks pure tasks in the object header, and compaction must not keep
that mark.
-/
unsafe def main : IO Unit := do
  let tmpFile : System.FilePath := "./_tmp_compact_task_sharing_test.olean"
  -- Read the value at run time so that the compiler cannot share the two tasks before compaction.
  let n := (← IO.monoMsNow) + 1000
  let tPure : Task Nat := Task.pure n
  let tSpawn : Task Nat := Task.spawn fun _ => n
  let _ := tSpawn.get
  let _ ← CompactedRegion.save tmpFile `test (tPure, tSpawn) #[] none
  let ((t1, t2), _region) ← CompactedRegion.read (α := Task Nat × Task Nat) tmpFile #[]
  IO.println s!"shared: {ptrAddrUnsafe t1 == ptrAddrUnsafe t2}"
  IO.FS.removeFile tmpFile
