import Std.Internal.UV.System

/-!
Process priorities at the edges. A priority outside the C `int` range is rejected instead of
wrapping, and pid 0 means the calling process. The priorities that are accepted are set on a child
process, so the test does not lower its own: 19 is accepted and read back, and a priority below -20
is rejected. A process that has exited and been reaped is reported as missing.
-/

open Std.Internal.UV

def check (name : String) (cond : Bool) (detail : String := "") : IO Unit :=
  unless cond do
    throw <| IO.userError s!"{name}: {detail}"

#eval do
  -- 2^32 plus the current priority, which would wrap to the current priority, so the call changes
  -- nothing even if it is not rejected.
  let pid ← System.osGetPid
  let current ← System.osGetPriority pid
  if let .ok _ ← (System.osSetPriority pid (current + 4294967296)).toBaseIO then
    throw <| IO.userError "priority out of the `int` range succeeded"

#eval do
  -- The test spawns `sleep` and `true`, which Windows does not have.
  if System.Platform.isWindows then
    return
  check "pid 0 is the calling process"
    ((← System.osGetPriority 0) == (← System.osGetPriority (← System.osGetPid)))

  let child ← IO.Process.spawn { cmd := "sleep", args := #["30"] }
  let pid := child.pid.toUInt64
  try
    System.osSetPriority pid 19
    let p ← System.osGetPriority pid
    check "priority 19" (p == 19) s!"{p}"
    -- -21 is below the -20 floor, which libuv rejects even with privileges.
    if let .ok _ ← (System.osSetPriority pid (-21)).toBaseIO then
      throw <| IO.userError "priority -21 succeeded"
  finally
    child.kill
    discard child.wait

  -- A new process may reuse a reaped pid, so only a pid found on every try fails the test.
  let mut found := #[]
  for _ in [0:3] do
    let reaped ← IO.Process.spawn { cmd := "true" }
    let pid := reaped.pid.toUInt64
    discard reaped.wait
    match ← (System.osGetPriority pid).toBaseIO with
    | .error (.noSuchThing ..) => return
    | .error e => throw <| IO.userError s!"reaped pid: unexpected error {e}"
    | .ok p => found := found.push (pid, p)
  throw <| IO.userError s!"reaped pids still have a priority: {found}"
