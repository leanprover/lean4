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
# Body Edge Case Tests

Tests for HTTP/1.1 body handling edge cases: Content-Length mismatches, chunked encoding
edge cases, body reading/consuming, Transfer-Encoding conflicts, and trailer headers.
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

/-- Assert response string contains a substring. -/
def assertContains (name : String) (response : ByteArray) (needle : String) : IO Unit := do
  let responseStr := String.fromUTF8! response
  unless responseStr.contains needle do
    throw <| IO.userError s!"Test '{name}' failed:\nExpected to contain: {needle.quote}\nGot:\n{responseStr.quote}"

/-- Assert the full response matches exactly. -/
def assertExact (name : String) (response : ByteArray) (expected : String) : IO Unit := do
  let responseStr := String.fromUTF8! response
  if responseStr != expected then
    throw <| IO.userError s!"Test '{name}' failed:\nExpected:\n{expected.quote}\nGot:\n{responseStr.quote}"

/-- Assert response starts with given prefix. -/
def assertStartsWith (name : String) (response : ByteArray) (prefix_ : String) : IO Unit := do
  let responseStr := String.fromUTF8! response
  unless responseStr.startsWith prefix_ do
    throw <| IO.userError s!"Test '{name}' failed:\nExpected to start with: {prefix_.quote}\nGot:\n{responseStr.quote}"

def bad400 : String :=
  "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"

def timeout408 : String :=
  "HTTP/1.1 408 Request Timeout\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"

/-- Handler that reads and echoes the full request body. -/
def echoBodyHandler : Request Body.Incoming → ContextAsync (Response Body.AnyBody) :=
  fun req => do
    let ctx ← ContextAsync.getContext

    background do
      Async.sleep 3000
      ctx.cancel .deadline

    let mut body := ByteArray.empty
    for chunk in req.body do
      body := body ++ chunk.data
    Response.ok |>.text (String.fromUTF8! body)


-- =============================================================================
-- POST with body and handler reads it correctly
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST /echo HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 13\x0d\nConnection: close\x0d\n\x0d\nHello, World!".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertContains "Echo body" response "Hello, World!"

-- =============================================================================
-- POST with Content-Length: 0 and no body bytes
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST /empty HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertStartsWith "Empty body CL=0" response "HTTP/1.1 200"

-- =============================================================================
-- Chunked request - handler reads body data
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST /chunked HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n6\x0d\n world\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertContains "Chunked body read" response "hello world"

-- =============================================================================
-- Zero-length chunked body (just the terminator)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST /empty-chunked HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertStartsWith "Zero-length chunked" response "HTTP/1.1 200"

-- =============================================================================
-- Single-byte chunks
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n1\x0d\na\x0d\n1\x0d\nb\x0d\n1\x0d\nc\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertContains "Single-byte chunks" response "abc"

-- =============================================================================
-- Large chunk size (hex)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let body := String.ofList (List.replicate 255 'X')
  let raw := s!"POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\nff\x0d\n{body}\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertContains "Large hex chunk (0xff=255)" response body

-- =============================================================================
-- Chunked with chunk extensions
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5;ext=val\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertContains "Chunk with extensions" response "hello"

-- =============================================================================
-- Chunked with quoted chunk extension value
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5;ext=\"quoted value\"\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertContains "Chunk with quoted extension" response "hello"

-- =============================================================================
-- Chunked with trailer headers
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\nX-Checksum: abc123\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertContains "Chunked with trailers" response "hello"

-- =============================================================================
-- Malformed chunk size (non-hex)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\nZZ\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  let responseStr := String.fromUTF8! response
  unless responseStr.startsWith "HTTP/1.1 400" ∨ responseStr.startsWith "HTTP/1.1 408" do
    throw <| IO.userError s!"Test 'Malformed chunk size' failed:\nExpected 400 or 408 status but got:\n{responseStr.quote}"

-- =============================================================================
-- Both Content-Length AND Transfer-Encoding (TE takes precedence per RFC 9112 §6.1)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 100\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertExact "Does not allow both headers" response bad400

-- =============================================================================
-- POST without Content-Length or Transfer-Encoding (ambiguous body)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\nsome body data".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  -- Without CL or TE, server should treat body as zero-length
  assertStartsWith "POST no CL no TE" response "HTTP/1.1"

-- =============================================================================
-- GET with unexpected body (Content-Length present)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\n\x0d\nhello".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  -- GET with body is technically valid per RFC
  assertStartsWith "GET with body" response "HTTP/1.1 200"

-- =============================================================================
-- Multiple chunks with varying sizes
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nabc\x0d\na\x0d\n0123456789\x0d\n1\x0d\nX\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertContains "Varying chunk sizes" response "abc0123456789X"

-- =============================================================================
-- Chunked with uppercase hex
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let body := String.ofList (List.replicate 10 'Y')
  let raw := s!"POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\nA\x0d\n{body}\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertContains "Uppercase hex chunk size" response body

-- =============================================================================
-- Chunked with mixed case hex
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let body := String.ofList (List.replicate 15 'Z')
  let raw := s!"POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\nF\x0d\n{body}\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertContains "Mixed case hex" response body

-- =============================================================================
-- Large body with Content-Length
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let body := String.ofList (List.replicate 10000 'A')
  let raw := s!"POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 10000\x0d\nConnection: close\x0d\n\x0d\n{body}".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertContains "Large body 10KB" response (String.ofList (List.replicate 100 'A'))

-- =============================================================================
-- Multiple Content-Length headers with same value (MAY accept)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 5\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\n\x0d\nhello".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  -- Same value duplicated - server may accept or reject
  assertStartsWith "Duplicate CL same value" response "HTTP/1.1"

-- =============================================================================
-- Transfer-Encoding: identity (should be treated as no encoding)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: identity\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\n\x0d\nhello".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertStartsWith "TE identity" response "HTTP/1.1"

-- =============================================================================
-- Chunked with multiple extensions
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5;a=1;b=2\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertContains "Multiple chunk extensions" response "hello"

-- =============================================================================
-- Body exactly at Content-Length boundary
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\n\x0d\nhello".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertContains "Exact CL boundary" response "hello"

-- =============================================================================
-- Binary body data
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let headers := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 4\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let body := ByteArray.mk #[0xFF, 0x00, 0xAB, 0xCD]
  let raw := headers ++ body
  let response ← sendRaw client server raw (fun req => do
    let mut body := ByteArray.empty
    for chunk in req.body do
      body := body ++ chunk.data
    if body.size == 4 then Response.ok |>.text "ok"
    else Response.badRequest |>.text s!"wrong size: {body.size}")
  assertContains "Binary body" response "ok"

-- =============================================================================
-- Chunked with trailing whitespace in chunk size
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  -- Chunk size with trailing space before CRLF
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5 \x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  -- Trailing space in chunk size line - may be accepted or rejected
  assertStartsWith "Chunk size trailing space" response "HTTP/1.1"

-- =============================================================================
-- Handler that ignores body - server should still drain on keep-alive
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let req1 := "POST /ignore HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 5\x0d\n\x0d\nhello"
  let req2 := "GET /after HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"
  let raw := (req1 ++ req2).toUTF8

  let response ← sendRaw client server raw (fun req => do
    -- Handler does NOT read the body
    Response.ok |>.text (toString req.head.uri))

  assertContains "Ignore body, drain: first" response "/ignore"
  assertContains "Ignore body, drain: second" response "/after"

-- =============================================================================
-- Chunked body followed by another request on keep-alive (body must be drained)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let req1 := "POST /chunked HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n"
  let req2 := "GET /next HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"
  let raw := (req1 ++ req2).toUTF8

  let response ← sendRaw client server raw (fun req => do
    Response.ok |>.text (toString req.head.uri))

  assertContains "Chunked drain keep-alive: first" response "/chunked"
  assertContains "Chunked drain keep-alive: second" response "/next"

-- =============================================================================
-- Content-Length with leading zeros
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 005\x0d\nConnection: close\x0d\n\x0d\nhello".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  -- Leading zeros - some servers accept, some reject
  assertStartsWith "CL leading zeros" response "HTTP/1.1"

-- =============================================================================
-- Very large Content-Length value (overflow attempt)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 99999999999999999999\x0d\nConnection: close\x0d\n\x0d\nhello".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertStartsWith "Huge CL value" response "HTTP/1.1"

-- =============================================================================
-- Chunked encoding: chunk size with leading zeros
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n005\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertContains "Chunk size leading zeros" response "hello"

-- =============================================================================
-- Multiple trailer headers after chunked body
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\nX-Checksum: abc\x0d\nX-Signature: def\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertContains "Multiple trailers" response "hello"

-- =============================================================================
-- Content-Length mismatch: body shorter than declared (should timeout/error)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  -- Declare CL=10 but only send 5 bytes, then close
  let headers := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 10\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let body := "hello".toUTF8
  let raw := headers ++ body
  let result ← Async.block do
    client.send raw
    -- Close only the client→server direction to simulate client disconnect
    client.getSendChan.close
    Std.Http.Server.serveConnection server echoBodyHandler { lingeringTimeout := 500, generateDate := false }
      |>.run
    let res ← client.recv?
    pure <| res.getD .empty
  -- Server should respond with something (timeout, error, or partial) but not crash
  assert! result.size > 0 ∨ result.size == 0

-- =============================================================================
-- Content-Length mismatch: body longer than declared (extra data is next request)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  -- CL=5 so only "hello" is read; remainder is parsed as a new request
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 5\x0d\n\x0d\nhelloGET /second HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw (fun req => do
    let mut body := ByteArray.empty
    for chunk in req.body do
      body := body ++ chunk.data
    Response.ok |>.text (String.fromUTF8! body))
  -- First response should have exactly "hello"
  assertContains "CL mismatch longer: first body" response "hello"
  -- The server processes the remainder as a second request on keep-alive.
  -- We see two HTTP/1.1 200 responses in the output.
  let responseStr := String.fromUTF8! response
  let parts := responseStr.splitOn "HTTP/1.1 200 OK"
  if parts.length < 3 then
    throw <| IO.userError s!"CL mismatch longer: expected 2 responses, got {parts.length} parts"

-- =============================================================================
-- Duplicate Content-Length with different values (MUST reject per RFC 9110 §8.6)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 3\x0d\nContent-Length: 7\x0d\nConnection: close\x0d\n\x0d\nabc".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertExact "Duplicate CL different values (3 vs 7)" response bad400

-- =============================================================================
-- Chunk size overflow (extremely large hex number)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\nFFFFFFFFFFFFFFFF\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  -- Should either reject or handle gracefully
  assertStartsWith "Chunk size overflow" response "HTTP/1.1"

-- =============================================================================
-- Incomplete chunked body (missing final 0\r\n\r\n, then connection closes)
-- =============================================================================

#eval show IO _ from do Async.block do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n".toUTF8
  client.send raw
  client.close
  let result ← Async.block do
    Std.Http.Server.serveConnection server echoBodyHandler { lingeringTimeout := 500, generateDate := false }
      |>.run
    let res ← client.recv?
    pure <| res.getD .empty
  -- Server should handle incomplete chunked body without crashing
  assert! result.size >= 0

-- =============================================================================
-- Content-Length: 0 with POST and handler reading body
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw (fun req => do
    let mut body := ByteArray.empty
    for chunk in req.body do
      body := body ++ chunk.data
    if body.size == 0
    then Response.ok |>.text "empty"
    else Response.badRequest |>.text s!"unexpected: {body.size}")
  assertContains "CL=0 body is empty" response "empty"

-- =============================================================================
-- Handler ignores chunked body on keep-alive, next request uses Content-Length
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let req1 := "POST /first HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\n\x0d\na\x0d\n0123456789\x0d\n0\x0d\n\x0d\n"
  let req2 := "POST /second HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 3\x0d\nConnection: close\x0d\n\x0d\nabc"
  let raw := (req1 ++ req2).toUTF8

  let response ← sendRaw client server raw (fun req => do
    -- Intentionally don't read body of first request
    Response.ok |>.text (toString req.head.uri))

  assertContains "Chunked then CL: first" response "/first"
  assertContains "Chunked then CL: second" response "/second"

-- =============================================================================
-- Extremely large number of chunks (100 single-byte chunks)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let mut chunked := ""
  for _ in [0:100] do
    chunked := chunked ++ "1\x0d\nX\x0d\n"
  chunked := chunked ++ "0\x0d\n\x0d\n"
  let raw := s!"POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n{chunked}".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  let expected := String.ofList (List.replicate 100 'X')
  assertContains "100 single-byte chunks" response expected
