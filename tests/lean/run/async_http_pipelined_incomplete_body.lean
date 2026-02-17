import Std.Internal.Http
import Std.Internal.Async

open Std.Internal.IO Async
open Std Http

abbrev TestHandler := Request Body.Incoming → ContextAsync (Response Body.Outgoing)

instance : Std.Http.Server.Handler TestHandler where
  onRequest handler request := handler request

def assertContains (name : String) (response : ByteArray) (needle : String) : IO Unit := do
  let responseStr := String.fromUTF8! response
  unless responseStr.contains needle do
    throw <| IO.userError s!"Test '{name}' failed:\nExpected to contain: {needle.quote}\nGot:\n{responseStr.quote}"

def assertNotContains (name : String) (response : ByteArray) (needle : String) : IO Unit := do
  let responseStr := String.fromUTF8! response
  if responseStr.contains needle then
    throw <| IO.userError s!"Test '{name}' failed:\nDid not expect to contain: {needle.quote}\nGot:\n{responseStr.quote}"

def assertCallCount (name : String) (seen : Array String) (expected : Nat) : IO Unit := do
  if seen.size != expected then
    throw <| IO.userError s!"Test '{name}' failed:\nExpected {expected} handler calls but saw {seen.size}: {seen}"

def runPipelined
    (raw : String)
    (readBody : Bool)
    (config : Config := { lingeringTimeout := 1000, generateDate := false }) : IO (ByteArray × Array String) := Async.block do
  let (client, server) ← Mock.new
  let seenRef ← IO.mkRef (#[] : Array String)

  let handler : TestHandler := fun req => do
    let uri := toString req.head.uri
    seenRef.modify (·.push uri)

    let body ← if readBody then req.body.readAll else pure "<ignored>"
    Response.ok |>.text s!"{uri}:{body}"

  client.send raw.toUTF8
  client.getSendChan.close

  Std.Http.Server.serveConnection server handler config
    |>.run

  let response ← client.recv?
  let seen ← seenRef.get
  pure (response.getD .empty, seen)

-- Incomplete first body with pipelined second request: second must not be processed.
#eval show IO _ from do
  let req1 := "POST /first HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 10\x0d\n\x0d\nabc"
  let req2 := "GET /second HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"
  let (response, seen) ← runPipelined (req1 ++ req2) true
  assertContains "Incomplete fixed body first request seen" response "/first"
  assertNotContains "Incomplete fixed body second request blocked" response "/second"
  assertCallCount "Incomplete fixed body call count" seen 1

-- Exact first body length: second pipelined request is processed.
#eval show IO _ from do
  let req1 := "POST /first HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 3\x0d\n\x0d\nabc"
  let req2 := "GET /second HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"
  let (response, seen) ← runPipelined (req1 ++ req2) true
  assertContains "Exact fixed body first request" response "/first"
  assertContains "Exact fixed body second request" response "/second"
  assertCallCount "Exact fixed body call count" seen 2

-- Handler ignores first body; server should drain and still process second request.
#eval show IO _ from do
  let req1 := "POST /ignored HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 5\x0d\n\x0d\nhello"
  let req2 := "GET /after HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"
  let (response, seen) ← runPipelined (req1 ++ req2) false
  assertContains "Ignored body first request" response "/ignored"
  assertContains "Ignored body second request" response "/after"
  assertCallCount "Ignored body drain call count" seen 2

-- Incomplete chunked first request with pipelined second request.
#eval show IO _ from do
  let req1 := "POST /chunked-first HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\n\x0d\nF\x0d\nhel"
  let req2 := "GET /second HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"
  let (response, seen) ← runPipelined (req1 ++ req2) true
  assertNotContains "Incomplete chunked should not process second" response "/second"
  if seen.contains "/second" then
    throw <| IO.userError s!"Test 'Incomplete chunked call list' failed: should not see /second, got {seen}"

-- Content-Length zero on first request should allow immediate parsing of second request.
#eval show IO _ from do
  let req1 := "POST /empty HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 0\x0d\n\x0d\n"
  let req2 := "GET /next HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"
  let (response, seen) ← runPipelined (req1 ++ req2) true
  assertContains "CL=0 first request" response "/empty"
  assertContains "CL=0 second request" response "/next"
  assertCallCount "CL=0 call count" seen 2

-- Complete chunked first request should allow next request on keep-alive.
#eval show IO _ from do
  let req1 := "POST /chunked HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n"
  let req2 := "GET /tail HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"
  let (response, seen) ← runPipelined (req1 ++ req2) true
  assertContains "Chunked first request" response "/chunked"
  assertContains "Chunked second request" response "/tail"
  assertCallCount "Chunked keep-alive call count" seen 2
