import Std.Async
import Std.Internal.UV.System
import Lean.Runtime

/-!
Process and group ids that do not fit the operating system's id types are rejected as invalid
arguments instead of being truncated to another process or group: a process id of 2^32 + 1 would
otherwise act on process 1, and a group id of 2^32 would otherwise look up group 0. This holds for
`Std.Async.System.getGroup` too, whose `GroupId` holds a `Nat`. The ids at the edge of the OS types
still reach the OS, `osGetPasswd` reports the uid and gid of the current user's passwd entry, and on
Windows `osGetGroup` reports the missing support for every id.
-/

open Std.Internal.UV

def expectError (what : String) (expected : IO.Error → Bool) (x : IO α) : IO Unit := do
  match ← x.toBaseIO with
  | .error e => unless expected e do throw <| IO.userError s!"{what}: unexpected error {e}"
  | .ok _ => throw <| IO.userError s!"{what}: succeeded"

def isInvalidArgument : IO.Error → Bool
  | .invalidArgument .. => true
  | _ => false

#eval do
  -- `uv_pid_t` is a signed 32-bit integer on every platform, so the first rejected id is 2^31.
  for (pid : Nat) in [2 ^ 31, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 32 + 1, 2 ^ 64 - 1] do
    expectError s!"getPriority {pid}" isInvalidArgument <| System.osGetPriority pid.toUInt64
    expectError s!"setPriority {pid}" isInvalidArgument <| System.osSetPriority pid.toUInt64 0
  if System.Platform.isWindows then
    return
  -- The largest `pid_t` passes the range check and reaches the OS, which finds no such process.
  let isNoSuchThing : IO.Error → Bool
    | .noSuchThing .. => true
    | _ => false
  expectError "getPriority (2^31 - 1)" isNoSuchThing <| System.osGetPriority (2 ^ 31 - 1)
  expectError "setPriority (2^31 - 1)" isNoSuchThing <| System.osSetPriority (2 ^ 31 - 1) 0

#eval do
  if System.Platform.isWindows || Lean.libUVVersion < 0x012D00 then
    return
  -- The id is a `Nat`, so ids of 2^64 and above must not wrap around to a small group either.
  for (gid : Nat) in [2 ^ 32, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 64 + 20, 2 ^ 200] do
    expectError s!"osGetGroup {gid}" isInvalidArgument <| System.osGetGroup gid
    expectError s!"getGroup {gid}" isInvalidArgument <| Std.Async.System.getGroup ⟨gid⟩
  -- The largest `gid_t` is looked up: no group on most systems, `nogroup` on macOS.
  match ← System.osGetGroup (2 ^ 32 - 1) with
  | none => pure ()
  | some g =>
    unless g.gid == 2 ^ 32 - 1 do
      throw <| IO.userError s!"getGroup (2^32 - 1): returned gid {g.gid}"

-- Windows has no group lookup. Every id reports that, including ids that do not fit libuv's
-- one-byte `uv_uid_t` there.
#eval do
  unless System.Platform.isWindows && Lean.libUVVersion >= 0x012D00 do
    return
  let isUnsupported : IO.Error → Bool
    | .unsupportedOperation .. => true
    | _ => false
  for (gid : Nat) in [0, 255, 256, 2 ^ 32, 2 ^ 64 - 1] do
    expectError s!"getGroup {gid}" isUnsupported <| System.osGetGroup gid

-- The uid and gid of the current user are both reported, and match the passwd entry as `id` reads
-- it. `id` is given the user name, since without one it reports the process's effective ids, which
-- differ from the passwd entry under `sg`, `sudo -g` or `docker --user`. A container may run under
-- a uid that has no passwd entry at all.
#eval show IO Unit from do
  if System.Platform.isWindows then
    return
  let r ← System.osGetPasswd.toBaseIO
  if let .error (.noSuchThing ..) := r then
    return
  let passwd ← match r with
    | .ok passwd => pure passwd
    | .error e => throw e
  let id (flag : String) : IO (Option UInt64) := do
    let out ← IO.Process.output { cmd := "id", args := #[flag, passwd.username] }
    return out.stdout.trimAscii.toNat?.map Nat.toUInt64
  let uid ← id "-u"
  let gid ← id "-g"
  unless passwd.uid.isSome && passwd.uid == uid do
    throw <| IO.userError s!"passwd uid {passwd.uid}, id -u {uid}"
  unless passwd.gid.isSome && passwd.gid == gid do
    throw <| IO.userError s!"passwd gid {passwd.gid}, id -g {gid}"
