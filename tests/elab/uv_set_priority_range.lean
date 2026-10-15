import Std.Internal.UV

/-!
`System.osSetPriority` rejects a priority outside the C `int` range instead of wrapping it.
-/

open Std.Internal.UV

#eval show IO Unit from do
  let pid := (← IO.Process.getPID).toUInt64
  let current ← System.osGetPriority pid
  -- 2^32 plus the current priority, which wraps to the current priority.
  if (← (System.osSetPriority pid (current + 4294967296)).toBaseIO) matches .ok _ then
    throw <| IO.userError "priority out of the `int` range succeeded"
