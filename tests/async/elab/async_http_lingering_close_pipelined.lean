import Std.Http
import Std.Http.Test.Helpers
import Std.Net.Addr

open Std.Async
open Std Http Internal Test
open Std.Net

/-!
Tests the lingering close (RFC 9112 §9.6) when the server ends a keep-alive connection while the
client pipelines. The handler answers `GET /a` after a delay, with `Connection: close` or as the last
request `maxRequests` allows, and the client sends `GET /b` meanwhile. The connection does not read
while a handler runs, so `GET /b` is still unread in the socket when the server closes, and closing a
socket with unread input sends a reset, which destroys the part of the response the client has not
read yet. The server has to shut down its write side and drain the input instead, so the client reads
the whole response and then the end of the stream.
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

def bodySize : Nat := 1024 * 1024

/--
Sends `GET /a`, then `GET /b` while the handler of `/a` sleeps, waits until the server has answered
`/a` and closed, and then reads. The client must read the whole 1 MiB answer to `/a` and no reset.
-/
def checkPipelinedClose (name : String) (config : Config) (closeHeader : Bool) : IO Unit :=
  withTimeout name 20000 <| Async.block do
    let handler := Server.Handler.ofFn fun _ => do
      sleep 100
      let builder := if closeHeader then Response.ok.header! "Connection" "close" else Response.ok
      builder.bytes (ByteArray.mk (Array.replicate bodySize 'x'.toUInt8))
    let server ← Server.serve (SocketAddressV4.mk (.ofParts 127 0 0 1) 0) handler config
    let some addr := server.localAddr | throw (IO.userError "the server has no address")
    let client ← TCP.Socket.Client.mk
    client.connect addr
    client.send (mkGet "/a").toUTF8
    sleep 20
    client.send (mkGet "/b").toUTF8
    sleep 300
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
    let headEnd := (text.splitOn "\x0d\n\x0d\n").headD ""
    let bodyRead := response.size - (headEnd.utf8ByteSize + 4)
    unless text.startsWith "HTTP/1.1 200" && text.contains "Connection: close" &&
        bodyRead == bodySize && recvError.isNone do
      throw <| IO.userError
        s!"'{name}': expected the whole answer to /a and no reset, got {bodyRead} of {bodySize} body bytes, receive error {recvError}"

#eval checkPipelinedClose "Connection: close from the handler"
  { defaultConfig with lingeringTimeout := 3000 } (closeHeader := true)

#eval checkPipelinedClose "maxRequests reached"
  { defaultConfig with lingeringTimeout := 3000, maxRequests := 1 } (closeHeader := false)
