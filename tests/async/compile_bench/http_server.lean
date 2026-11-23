import Std.Http.Test.Helpers

open Std.Async
open Std Http Internal Test

/-
Throughput benchmark for the HTTP/1.1 server request-handling loop.

We measure:
- `get_keepalive`: bare `GET`s answered with a small fixed body (no request body).
- `post_echo`: `POST`s with a fixed `Content-Length` body echoed back.
- `chunked_echo`: `POST`s with a `Transfer-Encoding: chunked` body echoed back.
- `many_headers`: `GET`s carrying several extra headers (header-parsing heavy).
-/

/--
Feed `n` pipelined requests to a fresh server connection, drive it to completion,
verify that exactly `n` responses came back, and report the wall-clock time.
-/
def runScenario (name : String) (n : Nat) (keep close : ByteArray) (handler : TestHandler) : IO Unit := do
  let cfg := { maxRequests := n, generateDate := false, lingeringTimeout := 1000 }
  let raw := buildPipeline n keep close
  let (client, server) ← Mock.new
  let t1 ← IO.monoMsNow

  let count ← Async.block do
    client.send raw
    client.getSendChan.close
    Std.Http.Server.serveConnection server handler cfg |>.run
    let res ← client.recv?
    pure (countResponses (res.getD .empty))

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
