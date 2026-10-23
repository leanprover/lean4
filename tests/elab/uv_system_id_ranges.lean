import Std.Internal.UV.System
import Lean.Runtime

/-!
Process and group ids that do not fit the operating system's id types are rejected as invalid arguments
instead of being truncated to another process or group: a process id of 2^32 + 1 would otherwise act on
process 1, and a group id of 2^32 would otherwise look up group 0 (PR #15653). The ids at the edge of
the OS types still reach the OS, `osGetPasswd` reports the gid of the current user, and on Windows
`osGetGroup` reports the missing support for every id.
-/

open Std.Internal.UV

def expectNoSuchProcess (what : String) (x : IO α) : IO Unit := do
  match ← x.toBaseIO with
  | .error (.noSuchThing ..) => pure ()
  | .error e => throw <| IO.userError s!"{what}: unexpected error {e}"
  | .ok _ => throw <| IO.userError s!"{what}: succeeded"

def expectInvalidArgument (what : String) (x : IO α) : IO Unit := do
  match ← x.toBaseIO with
  | .error (.invalidArgument ..) => pure ()
  | .error e => throw <| IO.userError s!"{what}: unexpected error {e}"
  | .ok _ => throw <| IO.userError s!"{what}: succeeded"

def expectUnsupported (what : String) (x : IO α) : IO Unit := do
  match ← x.toBaseIO with
  | .error (.unsupportedOperation ..) => pure ()
  | .error e => throw <| IO.userError s!"{what}: unexpected error {e}"
  | .ok _ => throw <| IO.userError s!"{what}: succeeded"

#eval do
  if System.Platform.isWindows then
    return
  -- `pid_t` is a signed 32-bit integer, so the first rejected id is 2^31.
  for (pid : Nat) in [2 ^ 31, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 32 + 1, 2 ^ 64 - 1] do
    expectInvalidArgument s!"getPriority {pid}" <| System.osGetPriority pid.toUInt64
    expectInvalidArgument s!"setPriority {pid}" <| System.osSetPriority pid.toUInt64 0
  -- The largest `pid_t` passes the range check and reaches the OS, which finds no such process.
  expectNoSuchProcess "getPriority (2^31 - 1)" <| System.osGetPriority (2 ^ 31 - 1)
  expectNoSuchProcess "setPriority (2^31 - 1)" <| System.osSetPriority (2 ^ 31 - 1) 0

#eval do
  if System.Platform.isWindows || Lean.libUVVersion < 0x012D00 then
    return
  -- The id is a `Nat`, so ids of 2^64 and above must not wrap around to a small group either.
  for (gid : Nat) in [2 ^ 32, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 64 + 20, 2 ^ 200] do
    expectInvalidArgument s!"getGroup {gid}" <| System.osGetGroup gid
  -- The largest `gid_t` is looked up: no group on most systems, `nogroup` on macOS.
  match ← System.osGetGroup (2 ^ 32 - 1) with
  | none => pure ()
  | some g =>
    unless g.gid == 2 ^ 32 - 1 do
      throw <| IO.userError s!"getGroup (2^32 - 1): returned gid {g.gid}"

-- Windows has no group lookup. Every id reports that, including ids that do not fit libuv's one-byte
-- `uv_uid_t` there.
#eval do
  unless System.Platform.isWindows && Lean.libUVVersion >= 0x012D00 do
    return
  for (gid : Nat) in [0, 255, 256, 2 ^ 32, 2 ^ 64 - 1] do
    expectUnsupported s!"getGroup {gid}" <| System.osGetGroup gid

-- The uid and gid of the current user are both reported, and match `id`.
#eval do
  if System.Platform.isWindows then
    return
  let passwd ← System.osGetPasswd
  let id (flag : String) : IO (Option UInt64) := do
    let out ← IO.Process.output { cmd := "id", args := #[flag] }
    return out.stdout.trimAscii.toNat?.map Nat.toUInt64
  let uid ← id "-u"
  let gid ← id "-g"
  unless passwd.uid.isSome && passwd.uid == uid do
    throw <| IO.userError s!"passwd uid {passwd.uid}, id -u {uid}"
  unless passwd.gid.isSome && passwd.gid == gid do
    throw <| IO.userError s!"passwd gid {passwd.gid}, id -g {gid}"
