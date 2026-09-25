import Std.Async
import Std.Internal.UV
import Std.Net.Addr

/-!
Tests that a second `accept` on a socket that already has one pending is rejected without leaving
the event loop mutex held. The rejection path used to return early while still holding the lock,
which starves the loop thread and stalls every later asynchronous operation.

Also checks that the rejection carries its explanation as a message rather than as a filename.
-/

open Std.Async
open Std.Net

def assertTrue (msg : String) (b : Bool) : IO Unit := do
  unless b do throw <| IO.userError msg

def parallelAccept : IO Unit := do
  let addr := SocketAddress.v4 <| SocketAddressV4.mk (.ofParts 127 0 0 1) 8271

  let server ← TCP.Socket.Server.mk
  server.bind addr
  server.listen 128

  -- Nothing is connecting, so this registers a pending accept instead of completing.
  let _pending ← server.native.accept

  let res ← (server.native.accept).toBaseIO

  match res with
  | .ok _ => throw <| IO.userError "expected the second accept to be rejected"
  | .error e =>
    let msg := toString e
    assertTrue s!"error should explain the parallel accept, got '{msg}'" <|
      (msg.splitOn "parallel accept").length == 2

  server.native.cancelAccept

  -- The loop must still make progress. Before the fix the rejection above kept the loop mutex, so
  -- the loop thread could never reacquire it and this sleep never completed.
  let sleeper ← (Std.Async.sleep 10).toIO
  discard sleeper.block

#eval parallelAccept
