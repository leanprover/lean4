import Std.Internal.UV

/-!
Size bounds of `Std.Internal.UV.System.random` (#14202): zero and small sizes produce that many
bytes, and sizes libuv cannot serve in one request fail with `E2BIG` without allocating the buffer.
-/

open Std.Internal.UV

def randomSize (n : UInt64) : IO (Except String Nat) := do
  try
    match ← IO.wait (← System.random n).result? with
    | some (.ok bytes) => return .ok bytes.size
    | some (.error e) => return .error (toString e)
    | none => return .error "dropped"
  catch e => return .error (toString e)

/-- info: ["ok: 0", "ok: 1", "ok: 4096", "error", "error"] -/
#guard_msgs in
#eval show IO _ from do
  let rs ← [0, 1, 4096, 0x80000000, 0xFFFFFFFFFFFFFFFF].mapM randomSize
  return rs.map fun
    | .ok n => s!"ok: {n}"
    | .error _ => "error"
