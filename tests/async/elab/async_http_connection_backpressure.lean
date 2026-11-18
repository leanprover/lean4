import Std.Http
import Std.Http.Test.Helpers

open Std.Async
open Std Http Internal Test

/-!
Tests that the server stops reading input it is not consuming. While a keep-alive response streams,
a client that floods bytes leaves most of them unread, instead of the connection buffering up to
`maxBodySize` plus the header limits.
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

#eval withTimeout "input flood during a streamed response" 10000 <| Async.block do
  let handler : TestHandler := fun _ =>
    Response.ok |>.stream fun out => do
      for i in [0:3] do
        out.send (Chunk.ofByteArray s!"[{i}]".toUTF8)
        sleep 100
  let (client, server) ← Mock.new
  client.send (mkGet "/").toUTF8
  let piece := ByteArray.mk (Array.replicate 65536 'x'.toUInt8)
  for _ in [0:64] do
    client.send piece
  Std.Http.Server.serveConnection server handler defaultConfig |>.run
  let mut response := ByteArray.empty
  repeat
    match ← client.tryRecv? with
    | some bytes => response := response ++ bytes
    | none => break
  unless (String.fromUTF8! response).contains "[2]" do
    throw (IO.userError "the streamed response was cut short")
  -- What the server never read is still queued.
  let mut unread := 0
  repeat
    match ← server.tryRecv? with
    | some bytes => unread := unread + bytes.size
    | none => break
  unless unread ≥ 3 * 1024 * 1024 do
    throw (IO.userError s!"the server read {64 * 65536 - unread} of the 4 MiB flood while the response streamed")
