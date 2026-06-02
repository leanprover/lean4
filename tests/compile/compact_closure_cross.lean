import Lean.CompactedRegion

open Lean

/-!
Tests that a closure saved via `CompactedRegion.save` with `allowClosures := true` in one process
loads and runs correctly in a *separate* process: the `v3` lib relocation table must re-point the
closure's fn pointer to the loader process's address space.
-/
unsafe def main (args : List String) : IO UInt32 := do
  let tmpFile : System.FilePath := "./_compact_closure_cross_test.olean"

  match args with
  | ["save"] =>
    let captured := "cross"
    let f : Nat → String := fun n => s!"{captured} {n}"
    let _ ← CompactedRegion.save tmpFile `test f #[] none true
    return 0
  | ["load"] =>
    let (g, _region) ← CompactedRegion.read (α := Nat → String) tmpFile #[]
    IO.println (g 7)
    IO.println (g 99)
    IO.FS.removeFile tmpFile
    return 0
  | _ =>
    -- Default: run save in one process, load in another
    let self ← IO.appPath
    let _ ← IO.Process.run { cmd := self.toString, args := #["save"] }
    let loadResult ← IO.Process.run { cmd := self.toString, args := #["load"] }
    IO.print loadResult
    return 0
