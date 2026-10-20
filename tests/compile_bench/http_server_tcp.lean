import Std.Http.Test.Helpers
import Std.Net.Addr

open Std.Async
open Std Http Internal Test
open Std.Net

/-
Throughput benchmark for the HTTP/1.1 server request-handling loop, driven over a real
loopback TCP connection (see `http_server.lean` for the in-memory `Mock` transport variant).
-/

def runScenario (name : String) (n : Nat) (keep close : ByteArray) (handler : TestHandler) : IO Unit := do
  let cfg := { maxRequests := n, generateDate := false, lingeringTimeout := 1000 }
  let raw := buildPipeline n keep close

  let (client, conn) ← Async.block do
    let server ← TCP.Socket.Server.mk
    server.bind (SocketAddressV4.mk (.ofParts 127 0 0 1) 0)
    server.listen 128
    server.noDelay
    let addr ← server.getSockName

    let client ← TCP.Socket.Client.mk
    client.connect addr
    let conn ← server.accept
    pure (client, conn)

  let t1 ← IO.monoMsNow

  let count ← Async.block do
    let serveTask ← async (Std.Http.Server.serveConnection conn handler cfg |>.run)
    client.send raw
    client.shutdown

    let mut result := ByteArray.empty
    repeat
      match ← client.recv? ((1 : UInt64) <<< 20) with
      | none => break
      | some chunk => result := result ++ chunk

    await serveTask
    pure (countResponses result)

  let t2 ← IO.monoMsNow

  unless count == n do
    throw <| IO.userError s!"{name}: expected {n} responses, got {count}"

  let time := (t2 - t1).toFloat / 1000.0
  IO.println s!"measurement: {name} {time} s"
where
  countResponses (bytes : ByteArray) : Nat :=
    String.fromUTF8! bytes
    |>.splitOn "HTTP/1.1 "
    |>.length
    |> (· - 1)

  buildPipeline (n : Nat) (keep close : ByteArray) : ByteArray := Id.run do
    let mut buf := ByteArray.empty
    for _ in *...(n - 1) do buf := buf ++ keep
    return buf ++ close

def main (args : List String) : IO Unit := do
  let n := args[0]!.toNat!

  -- Bare GETs, answered with a fixed "ok" body.
  runScenario "get_keepalive" n
    (mkGet "/bench").toUTF8
    (mkGetClose "/bench").toUTF8
    okHandler

  -- POSTs with a fixed-length body echoed back.
  let body := "hello, world!!!!"
  runScenario "post_echo" n
    (mkPost "/echo" body).toUTF8
    (mkPost "/echo" body "Connection: close\x0d\n").toUTF8
    echoHandler

  -- Chunked POSTs echoed back.
  let cbody := chunk "hello" ++ chunk "world" ++ chunkEnd
  runScenario "chunked_echo" n
    (mkChunked "/echo" cbody).toUTF8
    (mkChunked "/echo" cbody "Connection: close\x0d\n").toUTF8
    echoHandler

  -- Header-parsing heavy GETs.
  let extra := "X-A: 1\x0d\nX-B: 2\x0d\nX-C: 3\x0d\nX-D: 4\x0d\nX-E: 5\x0d\nX-F: 6\x0d\n"
  runScenario "many_headers" n
    (mkGet "/bench" extra).toUTF8
    (mkGet "/bench" (extra ++ "Connection: close\x0d\n")).toUTF8
    okHandler
