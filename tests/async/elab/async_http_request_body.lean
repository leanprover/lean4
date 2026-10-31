import Std.Http.Test.Helpers

open Std.Async
open Std Http Internal Test

/-!
The server hands the handler the request body bytes it has already received before running it.
These tests check that the body still reaches handlers that read it late, chunk by chunk, in part
or not at all, and bodies that arrive over several reads.
-/

/-- Suspends the handler for a few milliseconds. -/
private def pause : ContextAsync Unit := do
  let _ ← Selectable.one #[.case (← Selector.sleep 10) pure]

/-- Answers with one line per body chunk: its data, then its extension names. -/
private def chunkHandler : TestHandler := fun req => do
  let mut out := ""
  for chunk in req.body do
    let names := chunk.extensions.toList.map fun (name, _) => toString name
    out := out ++ String.fromUTF8! chunk.data ++ " " ++ ",".intercalate names ++ "\n"
  Response.ok |>.text out

/-- The bodies of the responses in `response`, in order. -/
private def bodies (response : ByteArray) : List String :=
  (String.fromUTF8! response).splitOn "HTTP/1.1 " |>.drop 1 |>.map fun part =>
    (part.splitOn "\x0d\n\x0d\n").getD 1 ""

private def assertBodies (response : ByteArray) (expected : List String) : IO Unit := do
  let got := bodies response
  unless got == expected do
    throw <| IO.userError s!"expected bodies {expected}, got {got}:\n{(String.fromUTF8! response).quote}"

/-- Sends `first`, starts the server, then sends `second` once the server has read `first`. -/
private def sendInTwoParts (first second : String) (handler : TestHandler)
    (config : Config := defaultConfig) : IO ByteArray :=
  Async.block do
    let (client, server) ← Mock.new
    client.send first.toUTF8
    let serve ← async (t := AsyncTask) (Std.Http.Server.serveConnection server handler config |>.run)
    let _ ← Selectable.one #[.case (← Selector.sleep 20) pure]
    client.send second.toUTF8
    await serve
    pure ((← client.recv?).getD .empty)

#eval runGroup "Body received with the head" do
  checkTimed "handler that suspends before reading gets the fixed-length body"
    (raw := mkPost "/" "hello" "Connection: close\x0d\n")
    (handler := fun req => do pause; Response.ok |>.text (← req.body.readAll))
    (expect := fun r => assertStatus r "HTTP/1.1 200" *> assertBodies r ["hello"])

  checkTimed "handler that suspends before reading gets the chunked body"
    (raw := mkChunked "/" (chunk "hello" ++ chunk "world" ++ chunkEnd) "Connection: close\x0d\n")
    (handler := fun req => do pause; Response.ok |>.text (← req.body.readAll))
    (expect := fun r => assertStatus r "HTTP/1.1 200" *> assertBodies r ["helloworld"])

  checkTimed "chunk boundaries and extensions are kept"
    (raw := mkChunked "/" ("5;a=1;b\x0d\nhello\x0d\n" ++ chunk "world" ++ chunkEnd) "Connection: close\x0d\n")
    (handler := chunkHandler)
    (expect := fun r => assertBodies r ["hello a,b\nworld \n"])

  checkTimed "pipelined requests whose handlers read all, part or none of the body"
    (raw := mkPost "/all" "one" ++ mkChunked "/part" (chunk "two" ++ chunk "three" ++ chunkEnd) ++
      mkPost "/none" "skipped" ++ mkGetClose "/last")
    (handler := fun req => do
      match toString req.line.uri with
      | "/all" => Response.ok |>.text (← req.body.readAll)
      | "/part" =>
        let first ← req.body.recv
        Response.ok |>.text (String.fromUTF8! (first.map (·.data) |>.getD .empty))
      | uri => Response.ok |>.text uri)
    (expect := fun r => assertBodies r ["one", "two", "/none", "/last"])

  -- The server already holds the bytes over the limit, but the request fails only once they are read.
  checkTimed "chunked body over the limit is accepted by a handler that does not read it"
    (raw := mkChunked "/" (chunk "hello" ++ chunk "world" ++ chunkEnd) "Connection: close\x0d\n")
    (handler := fun _ => Response.ok |>.text "ran")
    (expect := fun r => assertStatus r "HTTP/1.1 200" *> assertBodies r ["ran"])
    (config := { defaultConfig with maxBodySize := 8 })

  checkTimed "chunked body over the limit is answered with 413 once read"
    (raw := mkChunked "/" (chunk "hello" ++ chunk "world" ++ chunkEnd) "Connection: close\x0d\n")
    (handler := echoHandler)
    (expect := fun r => assertStatus r "HTTP/1.1 413")
    (config := { defaultConfig with maxBodySize := 8 })

#eval runGroup "Body split across reads" do
  let echo : TestHandler := fun req => do Response.ok |>.text (← req.body.readAll)

  let r ← sendInTwoParts
    ("POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 10\x0d\nConnection: close\x0d\n\x0d\nhello")
    "world" echo
  assertBodies r ["helloworld"]

  let r ← sendInTwoParts
    ("POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhel")
    ("lo\x0d\n" ++ chunk "world" ++ chunkEnd) echo
  assertBodies r ["helloworld"]

  -- The first chunk is split, so its two pieces are delivered as one chunk.
  let r ← sendInTwoParts
    ("POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5;a\x0d\nhel")
    ("lo\x0d\n" ++ chunk "world" ++ chunkEnd) chunkHandler
  assertBodies r ["hello a\nworld \n"]
