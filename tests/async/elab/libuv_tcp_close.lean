module

import Std.Async.Basic
import Std.Internal.UV.TCP

/-!
Tests `Std.Internal.UV.TCP.Socket.close`: the peer sees the connection end, closing twice does
nothing, every later operation fails, and pending reads, accepts and writes end with an error instead
of waiting, including a write blocked on a peer that does not read, when another thread closes the
socket.
-/

open Std Async Net Internal.UV

def blockPromise (promise : IO.Promise (Except IO.Error α)) : IO α :=
  AsyncTask.ofPromise promise |>.block

/-- Waits up to `ms` for `promise`, returning `none` if it is still pending. -/
def waitFor (promise : IO.Promise (Except IO.Error α)) (ms : Nat) : IO (Option (Except IO.Error α)) := do
  let task := promise.result?
  let mut waited := 0
  while !(← IO.hasFinished task) && waited < ms do
    IO.sleep 10
    waited := waited + 10
  if ← IO.hasFinished task then
    return task.get
  return none

def connectPair : IO (TCP.Socket × TCP.Socket) := do
  let server ← TCP.Socket.new
  server.bind <| SocketAddressV4.mk (.ofParts 127 0 0 1) 0
  server.listen 1
  let addr ← server.getSockName
  let acceptPromise ← server.accept
  let client ← TCP.Socket.new
  blockPromise (← client.connect addr)
  return (client, ← blockPromise acceptPromise)

def expectError (name : String) (action : IO α) : IO Unit := do
  match ← action.toBaseIO with
  | .error _ => pure ()
  | .ok _ => throw <| IO.userError s!"{name}: expected an error after close"

/-- Expects `promise` to fail within a second. -/
def expectFails (name : String) (promise : IO.Promise (Except IO.Error α)) : IO Unit := do
  match ← waitFor promise 1000 with
  | some (.error _) => pure ()
  | some (.ok _) => throw <| IO.userError s!"{name}: expected an error, got a result"
  | none => throw <| IO.userError s!"{name}: still pending a second after close"

-- The peer reads end-of-stream once the socket is closed.
#eval show IO Unit from do
  let (client, server) ← connectPair
  blockPromise (← server.send #["hi".toUTF8])
  server.close
  let some data ← blockPromise (← client.recv? 16) | throw <| IO.userError "expected the sent bytes"
  unless data == "hi".toUTF8 do throw <| IO.userError "wrong bytes"
  if let some more ← blockPromise (← client.recv? 16) then
    throw <| IO.userError s!"expected end-of-stream, got {more.size} bytes"

-- Closing twice does nothing, and every later operation fails.
#eval show IO Unit from do
  let (client, server) ← connectPair
  server.close
  server.close
  expectError "send" (do blockPromise (← server.send #["x".toUTF8]))
  expectError "recv?" (do blockPromise (← server.recv? 16))
  expectError "waitReadable" (do blockPromise (← server.waitReadable))
  expectError "shutdown" (do blockPromise (← server.shutdown))
  expectError "getPeerName" server.getPeerName
  expectError "getSockName" server.getSockName
  expectError "noDelay" server.noDelay
  expectError "keepAlive" (server.keepAlive 1 1)
  expectError "bind" (server.bind <| SocketAddressV4.mk (.ofParts 127 0 0 1) 0)
  expectError "listen" (server.listen 1)
  expectError "connect" (do blockPromise (← server.connect (← client.getSockName)))
  client.close

-- A pending read ends with an error when the socket is closed. Each pair closes the peer last: once
-- the peer closed, the socket is readable, so a read on it can legitimately finish first.
#eval show IO Unit from do
  let (client, server) ← connectPair
  let pending ← server.recv? 16
  server.close
  expectFails "pending recv?" pending
  client.close

#eval show IO Unit from do
  let (client, server) ← connectPair
  let pending ← client.waitReadable
  client.close
  expectFails "pending waitReadable" pending
  server.close

-- A pending accept ends with an error when the listening socket is closed.
#eval show IO Unit from do
  let listener ← TCP.Socket.new
  listener.bind <| SocketAddressV4.mk (.ofParts 127 0 0 1) 0
  listener.listen 1
  let pending ← listener.accept
  listener.close
  expectFails "pending accept" pending
  expectError "accept after close" (do blockPromise (← listener.accept))

-- A write blocked on a peer that does not read is cancelled by close, also from a thread other than
-- the one that issued it, and the peer then reaches end-of-stream. Windows accepts a whole write,
-- however large, while its send buffer has room, so pieces are written until one stays pending.
-- Windows still delivers the bytes of a cancelled write it already took, so the received count is
-- not checked.
#eval show IO Unit from do
  let (client, server) ← connectPair
  let piece := ByteArray.mk (Array.replicate (1024 * 1024) 0)
  let mut sent := 0
  let mut pending : Option (IO.Promise (Except IO.Error Unit)) := none
  while pending.isNone && sent < 256 * piece.size do
    let write ← server.send #[piece]
    sent := sent + piece.size
    if (← waitFor write 300).isNone then
      pending := some write
  let some write := pending
    | throw <| IO.userError s!"a peer that does not read took all {sent} bytes; no write stayed pending"
  IO.ofExcept (← IO.wait (← IO.asTask (prio := .dedicated) server.close))
  expectFails "pending write" write
  repeat
    match ← (do blockPromise (← client.recv? 65536)).toBaseIO with
    | .ok (some _) => pure ()
    | .ok none | .error _ => break
  client.close
