import Std.Http

open Std Std.Async Std.Http Std.Http.Internal

/-!
Tests `Outbox.maxWriteBytes`: a write longer than the bound is split, the bytes past it waiting in
the queue, and every byte still reaches the peer once and in order.
-/

/-- Sends `data` through an outbox bounded by `limit`; returns what `send` reported as queued and
what the peer received. -/
def sendBounded (limit : Option Nat) (data : String) : IO (Option Nat × String) := Async.block do
  let (client, server) ← Mock.new
  let outbox ← Outbox.new server 1000 limit
  let queued ← outbox.send (ChunkedBuffer.empty.push data.toUTF8)
  outbox.awaitIdle
  let mut received := ByteArray.empty
  while received.size < data.utf8ByteSize do
    match ← client.recv? with
    | some bytes => received := received ++ bytes
    | none => break
  outbox.stop
  return (queued, String.fromUTF8! received)

/-- info: (some 0, "0123456789") -/
#guard_msgs in
#eval sendBounded none "0123456789"

-- The first write carries 4 bytes; the 6 past the bound wait in the queue.
/-- info: (some 6, "0123456789") -/
#guard_msgs in
#eval sendBounded (some 4) "0123456789"

/-- info: (some 0, "abc") -/
#guard_msgs in
#eval sendBounded (some 4) "abc"
