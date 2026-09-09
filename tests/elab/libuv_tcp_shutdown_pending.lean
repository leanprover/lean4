module

import Std.Async.Basic
import Std.Internal.UV.TCP

/-!
Tests the error reported when a TCP shutdown is requested on a socket that already had one
requested, both while the first request is still pending and after it has finished.
-/

open Std Async Net Internal.UV

def blockPromise (promise : IO.Promise (Except IO.Error α)) : IO α :=
  AsyncTask.ofPromise promise |>.block

partial def recvBytes (socket : TCP.Socket) (remaining : Nat) : IO Unit := do
  if remaining == 0 then
    return
  let some chunk ← blockPromise (← socket.recv? remaining.toUInt64)
    | throw <| IO.userError "unexpected end of stream"
  recvBytes socket (remaining - chunk.size)

def connectPair : IO (TCP.Socket × TCP.Socket) := do
  let server ← TCP.Socket.new
  server.bind <| SocketAddressV4.mk (.ofParts 127 0 0 1) 0
  server.listen 1
  let addr ← server.getSockName

  let acceptPromise ← server.accept
  let client ← TCP.Socket.new
  blockPromise (← client.connect addr)
  return (client, ← blockPromise acceptPromise)

def shutdownError (socket : TCP.Socket) : IO String := do
  try
    discard socket.shutdown
    pure "no error"
  catch
    | .otherError _ message => pure message
    | error => pure s!"unexpected error: {error}"

def testPending : IO String := do
  let (client, accepted) ← connectPair

  let size := 8 * 1024 * 1024
  let payload := ByteArray.mk <| Array.replicate size 0
  let sendPromise ← client.send #[payload]
  let shutdownPromise ← client.shutdown
  let message ← shutdownError client

  recvBytes accepted size
  blockPromise sendPromise
  blockPromise shutdownPromise
  return message

def testFinished : IO String := do
  let (client, _accepted) ← connectPair
  blockPromise (← client.shutdown)
  shutdownError client

/-- info: "shutdown already requested" -/
#guard_msgs in
#eval testPending

/-- info: "shutdown already requested" -/
#guard_msgs in
#eval testFinished
