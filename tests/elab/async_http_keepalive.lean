import Std.Http.Test.Helpers

open Std.Async
open Std Http Internal Test

-- Helper: run pipelined raw request string, closing the client after send.
-- Returns (response bytes, list of URIs seen by the handler).
private def runPipelined
    (raw : String)
    (readBody : Bool := true)
    (config : Config := defaultConfig) : IO (ByteArray × Array String) := Async.block do
  let (client, server) ← Mock.new
  let seenRef ← IO.mkRef (#[] : Array String)

  let handler : TestHandler := fun req => do
    seenRef.modify (·.push (toString req.line.uri))
    let body ←
      if readBody then req.body.readAll
      else pure "<ignored>"
    Response.ok |>.text s!"{toString req.line.uri}:{body}"

  client.send raw.toUTF8
  client.getSendChan.close
  Std.Http.Server.serveConnection server handler config |>.run

  let response ← client.recv?
  let seen ← seenRef.get
  pure (response.getD .empty, seen)

private def assertSeenCount (seen : Array String) (expected : Nat) : IO Unit := do
  unless seen.size == expected do
    throw <| IO.userError s!"expected {expected} handler calls, got {seen.size}: {seen}"

-- HTTP/1.1 keep-alive behavior

#eval runGroup "Keep-alive: basic" do
  check "two sequential keep-alive requests → 2 responses"
    (raw :=
      "GET /first HTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n" ++
      "GET /second HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := fun req => Response.ok |>.text (toString req.line.uri))
    (expect := fun r =>
      assertResponseCount r 2 *>
      assertContains r "/first" *>
      assertContains r "/second")

  check "Connection: close on first request blocks pipelined second"
    (raw :=
      "GET /first HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n" ++
      "GET /second HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := fun req => Response.ok |>.text (toString req.line.uri))
    (expect := fun r =>
      assertResponseCount r 1 *>
      assertContains r "/first" *>
      assertAbsent r "/second")

  check "enableKeepAlive: false → one response only"
    (raw :=
      "GET /1 HTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n" ++
      "GET /2 HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := fun req => Response.ok |>.text (toString req.line.uri))
    (config := { defaultConfig with enableKeepAlive := false, lingeringTimeout := 3000 })
    (expect := fun r =>
      assertResponseCount r 1 *>
      assertContains r "/1" *>
      assertAbsent r "/2")

  check "maxRequests: 2 caps third request"
    (raw :=
      "GET /0 HTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n" ++
      "GET /1 HTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n" ++
      "GET /2 HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := fun req => Response.ok |>.text (toString req.line.uri))
    (config := { defaultConfig with maxRequests := 2, lingeringTimeout := 3000 })
    (expect := fun r =>
      assertResponseCount r 2 *>
      assertContains r "/0" *>
      assertContains r "/1" *>
      assertAbsent r "/2")

-- Body draining between keep-alive requests

#eval runGroup "Keep-alive: unread body draining" do
  check "handler ignores fixed-size body → next keep-alive works"
    (raw :=
      "POST /ignore HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 5\x0d\n\x0d\nhello" ++
      "GET /after HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := fun req => Response.ok |>.text (toString req.line.uri))
    (config := { defaultConfig with lingeringTimeout := 3000 })
    (expect := fun r =>
      assertResponseCount r 2 *>
      assertContains r "/ignore" *>
      assertContains r "/after")

  check "handler ignores chunked body → next keep-alive works"
    (raw :=
      "POST /chunked HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n" ++
      "GET /next HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := fun req => Response.ok |>.text (toString req.line.uri))
    (config := { defaultConfig with lingeringTimeout := 3000 })
    (expect := fun r =>
      assertResponseCount r 2 *>
      assertContains r "/chunked" *>
      assertContains r "/next")

-- Pipelining after exact Content-Length

#eval runGroup "Keep-alive: pipelined requests after exact CL" do
  let (response, seen) ← runPipelined
    ("POST /first HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 3\x0d\n\x0d\nabc" ++
     "GET /second HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")

  assertResponseCount response 2
  assertContains response "/first"
  assertContains response "/second"
  assertSeenCount seen 2

#eval runGroup "Keep-alive: incomplete body blocks pipelining" do
  let (response1, seen1) ← runPipelined
    ("POST /first HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 10\x0d\n\x0d\nabc" ++
     "GET /second HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")

  assertContains response1 "/first"
  assertAbsent response1 "/second"
  assertSeenCount seen1 1

  let (response2, _) ← runPipelined
    ("POST /chunked-first HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\n\x0d\nF\x0d\nhel" ++
     "GET /second HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")

  assertAbsent response2 "/second"

#eval runGroup "Keep-alive: CL=0 and complete chunked allow immediate next" do
  let (resp1, seen1) ← runPipelined
    ("POST /empty HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 0\x0d\n\x0d\n" ++
     "GET /tail HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")

  assertResponseCount resp1 2
  assertContains resp1 "/empty"
  assertContains resp1 "/tail"
  assertSeenCount seen1 2

  let (resp2, seen2) ← runPipelined
    ("POST /chunked HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n" ++
     "GET /tail HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")

  assertResponseCount resp2 2
  assertContains resp2 "/chunked"
  assertContains resp2 "/tail"
  assertSeenCount seen2 2
