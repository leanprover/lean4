import Lean.CompactedRegion

open Lean

/-!
Regression test that the `lean` driver runs its main logic on a thread with the configured
Lean thread stack size instead of directly on the OS main thread, whose fixed default stack
(often 8 MiB) is too small for the runtime's recursive algorithms. Exercises two stack-hungry
paths that run on the driver's main thread: interpreting a non-tail-recursive function at a
depth beyond the OS default stack's interpreter headroom, and compacting a deeply nested
object graph with `CompactedRegion.save`, whose compactor recurses once per nesting level.
-/

def depth : Nat := 100000

def deepRec : Nat → Nat
  | 0 => 0
  | n+1 => 1 + deepRec n

def mkDeepList (n : Nat) : List Nat := Id.run do
  let mut xs := []
  for i in [0:n] do
    xs := i :: xs
  return xs

unsafe def main : IO UInt32 := do
  unless deepRec depth == depth do
    throw <| IO.userError "deepRec mismatch"
  let tmpFile : System.FilePath := "./_tmp_shell_thread_stack.olean"
  let xs := mkDeepList (4 * depth)
  let _ ← CompactedRegion.save tmpFile `ShellThreadStack xs #[] none
  let (ys, _region) ← CompactedRegion.read (α := List Nat) tmpFile #[]
  unless ys.length == 4 * depth do
    throw <| IO.userError s!"round-trip length mismatch: expected {4 * depth}, got {ys.length}"
  IO.FS.removeFile tmpFile
  return 0
