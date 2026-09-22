import Std.Internal.UV

/-!
Size bounds of `Std.Internal.UV.System.random`: zero and small sizes produce that many bytes, and
sizes above 2^31 - 1 fail with `IO.Error.resourceExhausted`. Sizes the
allocator refuses (2^48, 2^63) or that overflow the array size (2^64 - 1) used to abort the process
before libuv could reject them.
-/

open Std.Internal.UV

def randomSize (n : UInt64) : IO (Except String Nat) := do
  try
    match ← IO.wait (← System.random n).result? with
    | some (.ok bytes) => return .ok bytes.size
    | some (.error e) => return .error (toString e)
    | none => return .error "dropped"
  catch e => return .error (toString e)

/-- info: ["ok: 0", "ok: 1", "ok: 4096", "error", "error", "error", "error"] -/
#guard_msgs in
#eval show IO _ from do
  let rs ← [0, 1, 4096, 0x80000000, 0x1000000000000, 0x8000000000000000, 0xFFFFFFFFFFFFFFFF].mapM
    randomSize
  return rs.map fun
    | .ok n => s!"ok: {n}"
    | .error _ => "error"
