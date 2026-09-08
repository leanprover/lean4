module

import Std.Async.Basic
import Std.Internal.UV.TCP

/-!
Tests the error reported when a TCP shutdown is requested while one is already pending.
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

def test : IO String := do
  let server ← TCP.Socket.new
  server.bind <| SocketAddressV4.mk (.ofParts 127 0 0 1) 0
  server.listen 1
  let addr ← server.getSockName

  let acceptPromise ← server.accept
  let client ← TCP.Socket.new
  let connectPromise ← client.connect addr
  blockPromise connectPromise
  let accepted ← blockPromise acceptPromise

  let size := 8 * 1024 * 1024
  let payload := ByteArray.mk <| Array.replicate size 0
  let sendPromise ← client.send #[payload]
  let shutdownPromise ← client.shutdown
  let message ← try
    discard client.shutdown
    pure "no error"
  catch
    | .otherError _ message => pure message
    | error => pure s!"unexpected error: {error}"

  recvBytes accepted size
  blockPromise sendPromise
  blockPromise shutdownPromise
  return message

/-- info: "shutdown already in progress" -/
#guard_msgs in
#eval test
