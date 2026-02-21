import Std.Internal.Http
import Std.Internal.Async

open Std.Internal.IO Async
open Std Http

abbrev TestHandler := Request Body.Incoming → ContextAsync (Response Body.AnyBody)

instance : Std.Http.Server.Handler TestHandler where
  onRequest handler request := handler request

instance : Coe (ContextAsync (Response Body.Incoming)) (ContextAsync (Response Body.AnyBody)) where
  coe action := do
    let response ← action
    pure { response with body := Body.Internal.incomingToOutgoing response.body }

instance : Coe (Async (Response Body.Incoming)) (ContextAsync (Response Body.AnyBody)) where
  coe action := do
    let response ← action
    pure { response with body := Body.Internal.incomingToOutgoing response.body }


def sendRaw
    (client : Mock.Client)
    (server : Mock.Server)
    (raw : ByteArray)
    (handler : TestHandler)
    (config : Config := { lingeringTimeout := 3000, generateDate := false }) : IO ByteArray := Async.block do
  client.send raw
  Std.Http.Server.serveConnection server handler config
    |>.run
  let res ← client.recv?
  pure <| res.getD .empty


def runPipelined
    (raw : String)
    (readBody : Bool)
    (config : Config := { lingeringTimeout := 1000, generateDate := false }) : IO (ByteArray × Array String) := Async.block do
  let (client, server) ← Mock.new
  let seenRef ← IO.mkRef (#[] : Array String)

  let handler : TestHandler := fun req => do
    let uri := toString req.head.uri
    seenRef.modify (·.push uri)

    let body ←
      if readBody then
        req.body.readAll
      else
        pure "<ignored>"

    Response.ok |>.text s!"{uri}:{body}"

  client.send raw.toUTF8
  client.getSendChan.close

  Std.Http.Server.serveConnection server handler config
    |>.run

  let response ← client.recv?
  let seen ← seenRef.get
  pure (response.getD .empty, seen)


def assertContains (name : String) (response : ByteArray) (needle : String) : IO Unit := do
  let text := String.fromUTF8! response
  unless text.contains needle do
    throw <| IO.userError s!"Test '{name}' failed:\nExpected to contain {needle.quote}\nGot:\n{text.quote}"


def assertNotContains (name : String) (response : ByteArray) (needle : String) : IO Unit := do
  let text := String.fromUTF8! response
  if text.contains needle then
    throw <| IO.userError s!"Test '{name}' failed:\nDid not expect {needle.quote}\nGot:\n{text.quote}"


def countOccurrences (s : String) (needle : String) : Nat :=
  if needle.isEmpty then
    0
  else
    (s.splitOn needle).length - 1


def assertStatusCount (name : String) (response : ByteArray) (expected : Nat) : IO Unit := do
  let text := String.fromUTF8! response
  let got := countOccurrences text "HTTP/1.1 "
  if got != expected then
    throw <| IO.userError s!"Test '{name}' failed:\nExpected {expected} responses, got {got}\n{text.quote}"


def assertSeenCount (name : String) (seen : Array String) (expected : Nat) : IO Unit := do
  if seen.size != expected then
    throw <| IO.userError s!"Test '{name}' failed:\nExpected {expected} handler calls, got {seen.size}: {seen}"


-- Two sequential requests on the same HTTP/1.1 connection.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let req1 := "GET /first HTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n"
  let req2 := "GET /second HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"
  let response ← sendRaw client server (req1 ++ req2).toUTF8 (fun req =>
    Response.ok |>.text (toString req.head.uri))

  assertStatusCount "Two keep-alive responses" response 2
  assertContains "Two keep-alive first" response "/first"
  assertContains "Two keep-alive second" response "/second"

-- Connection: close on first request blocks pipelined second request.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let req1 := "GET /first HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"
  let req2 := "GET /second HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"
  let response ← sendRaw client server (req1 ++ req2).toUTF8 (fun req =>
    Response.ok |>.text (toString req.head.uri))

  assertStatusCount "Connection close response count" response 1
  assertContains "Connection close first served" response "/first"
  assertNotContains "Connection close second blocked" response "/second"

-- Disabling keep-alive via config forces one response.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let req1 := "GET /1 HTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n"
  let req2 := "GET /2 HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"
  let response ← sendRaw client server (req1 ++ req2).toUTF8
    (fun req => Response.ok |>.text (toString req.head.uri))
    (config := { lingeringTimeout := 3000, enableKeepAlive := false, generateDate := false })

  assertStatusCount "Keep-alive disabled response count" response 1
  assertContains "Keep-alive disabled first served" response "/1"
  assertNotContains "Keep-alive disabled second blocked" response "/2"

-- maxRequests cap enforces hard limit on responses per connection.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let req0 := "GET /0 HTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n"
  let req1 := "GET /1 HTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n"
  let req2 := "GET /2 HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"
  let response ← sendRaw client server (req0 ++ req1 ++ req2).toUTF8
    (fun req => Response.ok |>.text (toString req.head.uri))
    (config := { lingeringTimeout := 3000, maxRequests := 2, generateDate := false })

  assertStatusCount "maxRequests response count" response 2
  assertContains "maxRequests /0 served" response "/0"
  assertContains "maxRequests /1 served" response "/1"
  assertNotContains "maxRequests /2 blocked" response "/2"

-- Handler that ignores a fixed-size body still allows next keep-alive request.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let req1 := "POST /ignore HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 5\x0d\n\x0d\nhello"
  let req2 := "GET /after HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"
  let response ← sendRaw client server (req1 ++ req2).toUTF8 (fun req =>
    Response.ok |>.text (toString req.head.uri))

  assertStatusCount "Unread CL body keep-alive responses" response 2
  assertContains "Unread CL body first" response "/ignore"
  assertContains "Unread CL body second" response "/after"

-- Handler that ignores chunked body still allows next keep-alive request.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let req1 := "POST /chunked HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n"
  let req2 := "GET /next HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"
  let response ← sendRaw client server (req1 ++ req2).toUTF8 (fun req =>
    Response.ok |>.text (toString req.head.uri))

  assertStatusCount "Unread chunked body keep-alive responses" response 2
  assertContains "Unread chunked first" response "/chunked"
  assertContains "Unread chunked second" response "/next"

-- Exact first Content-Length allows pipelined second request.
#eval show IO _ from do
  let req1 := "POST /first HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 3\x0d\n\x0d\nabc"
  let req2 := "GET /second HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"
  let (response, seen) ← runPipelined (req1 ++ req2) true

  assertStatusCount "Exact CL pipelined responses" response 2
  assertContains "Exact CL first" response "/first"
  assertContains "Exact CL second" response "/second"
  assertSeenCount "Exact CL seen count" seen 2

-- Incomplete first Content-Length blocks pipelined second request.
#eval show IO _ from do
  let req1 := "POST /first HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 10\x0d\n\x0d\nabc"
  let req2 := "GET /second HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"
  let (response, seen) ← runPipelined (req1 ++ req2) true

  assertContains "Incomplete CL first served" response "/first"
  assertNotContains "Incomplete CL second blocked" response "/second"
  assertSeenCount "Incomplete CL seen count" seen 1

-- Incomplete first chunked body blocks pipelined second request.
#eval show IO _ from do
  let req1 := "POST /chunked-first HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\n\x0d\nF\x0d\nhel"
  let req2 := "GET /second HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"
  let (response, seen) ← runPipelined (req1 ++ req2) true

  assertNotContains "Incomplete chunked second blocked" response "/second"
  if seen.contains "/second" then
    throw <| IO.userError s!"Test 'Incomplete chunked seen list' failed: {seen}"

-- Content-Length: 0 on first request allows immediate second request.
#eval show IO _ from do
  let req1 := "POST /empty HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 0\x0d\n\x0d\n"
  let req2 := "GET /tail HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"
  let (response, seen) ← runPipelined (req1 ++ req2) true

  assertStatusCount "CL=0 pipelined responses" response 2
  assertContains "CL=0 first" response "/empty"
  assertContains "CL=0 second" response "/tail"
  assertSeenCount "CL=0 seen count" seen 2

-- Complete chunked first request allows second request.
#eval show IO _ from do
  let req1 := "POST /chunked HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n"
  let req2 := "GET /tail HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"
  let (response, seen) ← runPipelined (req1 ++ req2) true

  assertStatusCount "Complete chunked pipelined responses" response 2
  assertContains "Complete chunked first" response "/chunked"
  assertContains "Complete chunked second" response "/tail"
  assertSeenCount "Complete chunked seen count" seen 2
