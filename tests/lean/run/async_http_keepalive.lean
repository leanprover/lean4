import Std.Internal.Http
import Std.Internal.Async
import Std.Internal.Async.Timer

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


/-!
# Keep-Alive and Connection Persistence Tests

Tests for HTTP/1.1 keep-alive behavior, connection reuse, multiple sequential requests
on a single connection, and connection limits.
-/

/-- Send raw bytes to the server and return the response. -/
def sendRaw (client : Mock.Client) (server : Mock.Server) (raw : ByteArray)
    (handler : Request Body.Incoming → ContextAsync (Response Body.AnyBody))
    (config : Config := { lingeringTimeout := 3000, generateDate := false }) : IO ByteArray := Async.block do
  client.send raw
  Std.Http.Server.serveConnection server handler config
    |>.run
  let res ← client.recv?
  pure <| res.getD .empty

/-- Assert the full response matches exactly. -/
def assertExact (name : String) (response : ByteArray) (expected : String) : IO Unit := do
  let responseStr := String.fromUTF8! response
  if responseStr != expected then
    throw <| IO.userError s!"Test '{name}' failed:\nExpected:\n{expected.quote}\nGot:\n{responseStr.quote}"

/-- Assert response string contains a substring. -/
def assertContains (name : String) (response : ByteArray) (needle : String) : IO Unit := do
  let responseStr := String.fromUTF8! response
  unless responseStr.contains needle do
    throw <| IO.userError s!"Test '{name}' failed:\nExpected to contain: {needle.quote}\nGot:\n{responseStr.quote}"

/-- Assert response starts with given prefix. -/
def assertStartsWith (name : String) (response : ByteArray) (prefix_ : String) : IO Unit := do
  let responseStr := String.fromUTF8! response
  unless responseStr.startsWith prefix_ do
    throw <| IO.userError s!"Test '{name}' failed:\nExpected to start with: {prefix_.quote}\nGot:\n{responseStr.quote}"

/-- Count occurrences of a substring in a string. -/
partial def countOccurrences (haystack : String) (needle : String) : Nat :=
  let rec go (s : haystack.Pos) (count : Nat) : Nat :=
    if let some idx := s.find? needle then
      go (idx.nextn needle.length) (count + 1)
    else
      count

  go haystack.startPos 0


def okHandler : Request Body.Incoming → ContextAsync (Response Body.AnyBody) :=
  fun _ => Response.ok |>.text "ok"

-- =============================================================================
-- Two sequential requests on the same keep-alive connection
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let req1 := "GET /first HTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n"
  let req2 := "GET /second HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"
  let raw := (req1 ++ req2).toUTF8

  let response ← sendRaw client server raw (fun req => do
    let uri := toString req.head.uri
    if uri == "/first" then Response.ok |>.text "first"
    else if uri == "/second" then Response.ok |>.text "second"
    else Response.notFound |>.text "not found")

  assertContains "Keep-alive: two responses" response "HTTP/1.1 200 OK"
  assertContains "Keep-alive: first body" response "first"
  assertContains "Keep-alive: second body" response "second"

-- =============================================================================
-- Three sequential requests on keep-alive
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let req1 := "GET /a HTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n"
  let req2 := "GET /b HTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n"
  let req3 := "GET /c HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"
  let raw := (req1 ++ req2 ++ req3).toUTF8

  let response ← sendRaw client server raw (fun req => do
    let uri := toString req.head.uri
    Response.ok |>.text uri)

  let responseStr := String.fromUTF8! response
  assertContains "Three keep-alive: response a" response "/a"
  assertContains "Three keep-alive: response b" response "/b"
  assertContains "Three keep-alive: response c" response "/c"

-- =============================================================================
-- Explicit Connection: keep-alive header
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let req1 := "GET /1 HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: keep-alive\x0d\n\x0d\n"
  let req2 := "GET /2 HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"
  let raw := (req1 ++ req2).toUTF8

  let response ← sendRaw client server raw (fun req => do
    Response.ok |>.text (toString req.head.uri))

  assertContains "Explicit keep-alive: first" response "/1"
  assertContains "Explicit keep-alive: second" response "/2"

-- =============================================================================
-- Connection: close on first request - server should not process second
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let req1 := "GET /first HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"
  let req2 := "GET /second HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"
  let raw := (req1 ++ req2).toUTF8

  let response ← sendRaw client server raw (fun req => do
    Response.ok |>.text (toString req.head.uri))

  let responseStr := String.fromUTF8! response
  assertContains "Connection close: first served" response "/first"
  -- Second request should NOT be processed since first had Connection: close
  if responseStr.contains "/second" then
    throw <| IO.userError "Test 'Connection close stops pipeline' failed: second request was served"

-- =============================================================================
-- Default keep-alive (no Connection header = keep-alive in HTTP/1.1)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  -- No Connection header at all - HTTP/1.1 defaults to keep-alive
  let req1 := "GET /default1 HTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n"
  let req2 := "GET /default2 HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"
  let raw := (req1 ++ req2).toUTF8

  let response ← sendRaw client server raw (fun req => do
    Response.ok |>.text (toString req.head.uri))

  assertContains "Default keep-alive: first" response "/default1"
  assertContains "Default keep-alive: second" response "/default2"

-- =============================================================================
-- Keep-alive disabled via config
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let req1 := "GET /1 HTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n"
  let req2 := "GET /2 HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"
  let raw := (req1 ++ req2).toUTF8

  let response ← sendRaw client server raw
    (fun req => Response.ok |>.text (toString req.head.uri))
    (config := { lingeringTimeout := 3000, enableKeepAlive := false, generateDate := false })

  let responseStr := String.fromUTF8! response
  assertContains "Keep-alive disabled: first served" response "/1"
  -- With keep-alive disabled, second request should not be processed
  if responseStr.contains "/2" then
    throw <| IO.userError "Test 'Keep-alive disabled' failed: second request was served"

-- =============================================================================
-- Max requests per connection limit
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let config : Config := { lingeringTimeout := 3000, maxRequests := 3, generateDate := false }

  -- Send 4 requests but only 3 should be processed
  let mut raw := ""
  for i in [0:3] do
    raw := raw ++ s!"GET /{i} HTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n"
  raw := raw ++ "GET /3 HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"

  let response ← sendRaw client server raw.toUTF8
    (fun req => Response.ok |>.text (toString req.head.uri))
    (config := config)

  assertContains "Max requests: /0 served" response "/0"
  assertContains "Max requests: /1 served" response "/1"
  assertContains "Max requests: /2 served" response "/2"

-- =============================================================================
-- Keep-alive with POST bodies (body must be fully consumed before next request)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let req1 := "POST /upload HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 5\x0d\n\x0d\nhello"
  let req2 := "GET /after HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"
  let raw := (req1 ++ req2).toUTF8

  let response ← sendRaw client server raw (fun req => do
    let uri := toString req.head.uri
    if uri == "/upload" then Response.ok |>.text "uploaded"
    else if uri == "/after" then Response.ok |>.text "after"
    else Response.notFound |>.text "")

  assertContains "Keep-alive POST then GET: uploaded" response "uploaded"
  assertContains "Keep-alive POST then GET: after" response "after"

-- =============================================================================
-- Keep-alive response should include Connection header appropriately
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  -- First request without Connection: close - response should NOT have Connection: close
  let req1 := "GET /check HTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n"
  let req2 := "GET /end HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"
  let raw := (req1 ++ req2).toUTF8

  let response ← sendRaw client server raw okHandler

  assertContains "Last response has Connection: close" response "Connection: close"

-- =============================================================================
-- Mixed methods on keep-alive
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let req1 := "GET /get HTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n"
  let req2 := "POST /post HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 4\x0d\n\x0d\ndata"
  let req3 := "DELETE /delete HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"
  let raw := (req1 ++ req2 ++ req3).toUTF8

  let response ← sendRaw client server raw (fun req => do
    match req.head.method with
    | .get => Response.ok |>.text "got"
    | .post => Response.ok |>.text "posted"
    | .delete => Response.ok |>.text "deleted"
    | _ => Response.badRequest |>.text "unknown")

  assertContains "Mixed methods: got" response "got"
  assertContains "Mixed methods: posted" response "posted"
  assertContains "Mixed methods: deleted" response "deleted"

-- =============================================================================
-- Keep-alive with chunked request body then another request
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let req1 := "POST /chunked HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n"
  let req2 := "GET /after HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"
  let raw := (req1 ++ req2).toUTF8

  let response ← sendRaw client server raw (fun req => do
    Response.ok |>.text (toString req.head.uri))

  assertContains "Chunked then GET: first" response "/chunked"
  assertContains "Chunked then GET: second" response "/after"

-- =============================================================================
-- Keep-alive with varying Content-Lengths
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let req1 := "POST /a HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 3\x0d\n\x0d\nabc"
  let req2 := "POST /b HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 10\x0d\n\x0d\n0123456789"
  let req3 := "POST /c HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\n\x0d\n"
  let raw := (req1 ++ req2 ++ req3).toUTF8

  let response ← sendRaw client server raw (fun req => do
    Response.ok |>.text (toString req.head.uri))

  assertContains "Varying CL: /a" response "/a"
  assertContains "Varying CL: /b" response "/b"
  assertContains "Varying CL: /c" response "/c"

-- =============================================================================
-- Handler reads body on keep-alive connection
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let req1 := "POST /read HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 5\x0d\n\x0d\nhello"
  let req2 := "POST /read HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\n\x0d\nworld"
  let raw := (req1 ++ req2).toUTF8

  let response ← sendRaw client server raw (fun req => do
    let mut body := ByteArray.empty
    for chunk in req.body do
      body := body ++ chunk.data
    let bodyStr := String.fromUTF8! body
    Response.ok |>.text s!"body={bodyStr}")

  assertContains "Body read keep-alive: first" response "body=hello"
  assertContains "Body read keep-alive: second" response "body=world"
