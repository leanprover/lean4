import Std.Internal.Http
import Std.Internal.Async
import Std.Internal.Async.Timer

open Std.Internal.IO Async
open Std Http

/-!
# Body Edge Case Tests

Tests for HTTP/1.1 body handling edge cases: Content-Length mismatches, chunked encoding
edge cases, body reading/consuming, Transfer-Encoding conflicts, and trailer headers.
-/

/-- Send raw bytes to the server and return the response. -/
def sendRaw (client : Mock.Client) (server : Mock.Server) (raw : ByteArray)
    (handler : Request Body.Stream → ContextAsync (Response Body.Stream))
    (config : Config := { lingeringTimeout := 3000 }) : IO ByteArray := Async.block do
  client.send raw
  Std.Http.Server.serveConnection server handler (fun _ => pure ()) (config := config)
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

/-- Handler that reads and echoes the full request body. -/
def echoBodyHandler : Request Body.Stream → ContextAsync (Response Body.Stream) :=
  fun req => do
    let ctx ← ContextAsync.getContext

    background do
      Async.sleep 2000
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
  assertExact "Malformed chunk size" response bad400

-- =============================================================================
-- Both Content-Length AND Transfer-Encoding (TE takes precedence per RFC 9112 §6.1)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  -- When both are present, Transfer-Encoding takes precedence
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 100\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  -- Server should use chunked encoding (5 bytes "hello"), not Content-Length (100 bytes)
  assertContains "TE over CL: body correct" response "hello"

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
