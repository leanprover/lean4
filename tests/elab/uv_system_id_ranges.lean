import Std.Internal.UV.System
import Lean.Runtime

/-!
Process and group ids that do not fit the operating system's id types are rejected as invalid arguments
instead of being truncated to another process or group: a process id of 2^32 + 1 would otherwise act on
process 1, and a group id of 2^32 would otherwise look up group 0.
-/

open Std.Internal.UV

def expectInvalidArgument (what : String) (x : IO α) : IO Unit := do
  match ← x.toBaseIO with
  | .error (.invalidArgument ..) => pure ()
  | .error e => throw <| IO.userError s!"{what}: unexpected error {e}"
  | .ok _ => throw <| IO.userError s!"{what}: succeeded"

#eval do
  if System.Platform.isWindows then
    return
  expectInvalidArgument "getPriority (2^32 + 1)" <| System.osGetPriority (2 ^ 32 + 1)
  expectInvalidArgument "setPriority (2^32 + 1)" <| System.osSetPriority (2 ^ 32 + 1) 0

#eval do
  if System.Platform.isWindows || Lean.libUVVersion < 0x012D00 then
    return
  expectInvalidArgument "getGroup (2^32)" <| System.osGetGroup (2 ^ 32)
