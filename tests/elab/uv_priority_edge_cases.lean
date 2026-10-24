import Std.Internal.UV.System

/-!
Process priorities at the edges (PR #15653), on a child process so the test does not lower its own
priority: pid 0 means the calling process, 19 is accepted and read back, a priority below -20 is
rejected, and a process that has exited and been reaped is reported as missing.
-/

open Std.Internal.UV

def check (name : String) (cond : Bool) (detail : String := "") : IO Unit :=
  unless cond do
    throw <| IO.userError s!"{name}: {detail}"

#eval do
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
    -- Raising a priority above -20 is out of range, and not permitted without privileges anyway.
    if let .ok _ ← (System.osSetPriority pid (-21)).toBaseIO then
      throw <| IO.userError "priority -21 succeeded"
  finally
    child.kill
    discard child.wait

  let reaped ← IO.Process.spawn { cmd := "true" }
  let pid := reaped.pid.toUInt64
  discard reaped.wait
  match ← (System.osGetPriority pid).toBaseIO with
  | .error (.noSuchThing ..) => pure ()
  | .error e => throw <| IO.userError s!"reaped pid: unexpected error {e}"
  | .ok p => throw <| IO.userError s!"reaped pid: priority {p}"
