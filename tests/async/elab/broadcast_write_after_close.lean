import Std.Sync
import Std.Async

/-!
Writing to a closed `Broadcast` through `AsyncWrite` must throw, as sending to it does.
-/

open Std Async

#eval show IO Unit from do
  let b ← Broadcast.new (α := Nat)
  let _receiver ← b.subscribe
  b.close
  let result ← ((Std.Async.IO.AsyncWrite.write b 1 : Async Unit).block).toBaseIO
  if result matches .ok _ then
    throw <| IO.userError "write to a closed broadcast succeeded"
