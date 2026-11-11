import Std.Http
import Std.Http.Test.Helpers
import Std.Net.Addr

open Std.Async
open Std Http Internal Test
open Std.Net

/-!
Tests the lingering close (RFC 9112 §9.6). When the server answers `413` to an upload far over
`maxBodySize`, the client is still sending. The server shuts down its write side and drains the
input before closing, so the client neither gets a reset on its sends nor loses the response.
-/

def withTimeout {α : Type} (name : String) (ms : Nat) (action : IO α) : IO α := do
  let task ← IO.asTask action
  let rec loop : Nat → IO α
    | 0 => do
      IO.cancel task
      throw <| IO.userError s!"'{name}' did not finish within {ms} ms"
    | n + 1 => do
      if (← IO.getTaskState task) == .finished then
        match ← IO.wait task with
        | .ok x => pure x
        | .error e => throw e
      else
        IO.sleep 10
        loop n
  loop ((ms + 9) / 10)

#eval withTimeout "lingering close after 413" 20000 <| Async.block do
  let config := { defaultConfig with maxBodySize := 1024, lingeringTimeout := 3000 }
  let server ← Server.serve (SocketAddressV4.mk (.ofParts 127 0 0 1) 0) okHandler config
  let some addr := server.localAddr | throw (IO.userError "the server has no address")
  let client ← TCP.Socket.Client.mk
  client.connect addr
  let pieces := 64
  let piece := ByteArray.mk (Array.replicate 65536 'x'.toUInt8)
  client.send s!"POST / HTTP/1.1\x0d\nHost: a\x0d\nContent-Length: {pieces * piece.size}\x0d\n\x0d\n".toUTF8
  let mut sendError : Option String := none
  for _ in [0:pieces] do
    try client.send piece
    catch e =>
      sendError := some (toString e)
      break
  let mut response := ByteArray.empty
  let mut recvError : Option String := none
  repeat
    try
      match ← client.recv? 65536 with
      | none => break
      | some bytes => response := response ++ bytes
    catch e =>
      recvError := some (toString e)
      break
  server.shutdownAndWait
  let text := String.fromUTF8! response
  unless text.startsWith "HTTP/1.1 413" && sendError.isNone && recvError.isNone do
    throw <| IO.userError
      s!"expected the 413 and no reset, got {(text.take 40).toString.quote}, send error {sendError}, receive error {recvError}"
