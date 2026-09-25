import Std.Sync

/-!
Closing a bounded channel or a broadcast must complete the sends still blocked on its full buffer
with an error, as the documentation of `send` states, instead of leaving them pending until a
receiver makes room. (A send blocked on a zero-capacity channel is a value that can still be
received after the close, which `sync_channel` covers.)
-/

open Std

def expectClosedError {ε : Type} (what : String) (t : Task (Except ε α)) : IO Unit := do
  IO.sleep 100
  unless ← IO.hasFinished t do
    throw <| IO.userError s!"{what}: send still pending after close"
  if t.get matches .ok _ then
    throw <| IO.userError s!"{what}: send succeeded after close"

#eval show IO Unit from do
  let ch ← CloseableChannel.new (α := Nat) (some 1)
  let s1 ← ch.send 1
  let s2 ← ch.send 2
  discard <| EIO.toBaseIO ch.close
  unless (← IO.wait s1) matches .ok _ do
    throw <| IO.userError "bounded channel: first send failed"
  expectClosedError "bounded channel" s2
  -- Keeps `ch` alive until here: dropping it would drop the pending send's promise and fail the
  -- send without `close` doing anything.
  discard <| ch.isClosed

#eval show IO Unit from do
  let b ← Broadcast.new (α := Nat) 1
  let _receiver ← b.subscribe
  let s1 ← b.send 1
  let s2 ← b.send 2
  b.close
  unless (← IO.wait s1) matches .ok _ do
    throw <| IO.userError "broadcast: first send failed"
  expectClosedError "broadcast" s2
  discard <| b.trySend 0
