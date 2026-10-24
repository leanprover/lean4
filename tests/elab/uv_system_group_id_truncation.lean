import Std.Async
import Lean.Runtime

/-!
`Std.Async.System.getGroup` takes a `GroupId` holding a `Nat`. A group id that does not fit the
operating system's id type must be rejected as an invalid argument, like `osGetGroup` does since
PR #15653, instead of being truncated modulo 2^64: `GroupId.mk (2^64)` must not look up group 0, and
`GroupId.mk (2^64 + 20)` must not look up group 20.
-/

open Std.Async

def expectInvalidArgument (what : String) (x : IO α) : IO Unit := do
  match ← x.toBaseIO with
  | .error (.invalidArgument ..) => pure ()
  | .error e => throw <| IO.userError s!"{what}: unexpected error {e}"
  | .ok _ => throw <| IO.userError s!"{what}: succeeded"

#eval do
  if System.Platform.isWindows || Lean.libUVVersion < 0x012D00 then
    return
  expectInvalidArgument "getGroup (2^64)" <| System.getGroup ⟨2 ^ 64⟩
  expectInvalidArgument "getGroup (2^64 + 20)" <| System.getGroup ⟨2 ^ 64 + 20⟩
