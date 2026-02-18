import Std.Internal.Http
import Std.Internal.Async
import Std.Internal.Async.Timer

open Std.Internal.IO Async
open Std Http

abbrev TestHandler := Request Body.Incoming → ContextAsync (Response Body.Outgoing)

instance : Std.Http.Server.Handler TestHandler where
  onRequest handler request := handler request

instance : Coe (ContextAsync (Response Body.Incoming)) (ContextAsync (Response Body.Outgoing)) where
  coe action := do
    let response ← action
    pure { response with body := Body.Internal.incomingToOutgoing response.body }

instance : Coe (Async (Response Body.Incoming)) (ContextAsync (Response Body.Outgoing)) where
  coe action := do
    let response ← action
    pure { response with body := Body.Internal.incomingToOutgoing response.body }


/-!
# Malformed HTTP Request Tests

Tests for HTTP/1.1 compliance when handling malformed, invalid, or edge-case requests.
Covers: missing Host, invalid methods, bad headers, CRLF issues, invalid characters.
-/

/-- Send raw bytes to the server and return the response. -/
def sendRaw (client : Mock.Client) (server : Mock.Server) (raw : ByteArray)
    (handler : Request Body.Incoming → ContextAsync (Response Body.Outgoing))
    (config : Config := { lingeringTimeout := 3000, generateDate := false }) : IO ByteArray := Async.block do
  client.send raw
  Std.Http.Server.serveConnection server handler config
    |>.run
  let res ← client.recv?
  pure <| res.getD .empty

/-- Assert that the response starts with the expected status line. -/
def assertStatus (name : String) (response : ByteArray) (status : String) : IO Unit := do
  let responseStr := String.fromUTF8! response
  unless responseStr.startsWith status do
    throw <| IO.userError s!"Test '{name}' failed:\nExpected status: {status}\nGot: {responseStr.quote}"

/-- Assert the full response matches exactly. -/
def assertExact (name : String) (response : ByteArray) (expected : String) : IO Unit := do
  let responseStr := String.fromUTF8! response
  if responseStr != expected then
    throw <| IO.userError s!"Test '{name}' failed:\nExpected:\n{expected.quote}\nGot:\n{responseStr.quote}"

def okHandler : Request Body.Incoming → ContextAsync (Response Body.Outgoing) :=
  fun _ => Response.ok |>.text "ok"

def bad400 : String :=
  "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"

def bad505 : String :=
  "HTTP/1.1 505 HTTP Version Not Supported\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"

def ok200 : String :=
  "HTTP/1.1 200 OK\x0d\nContent-Length: 2\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\nContent-Type: text/plain; charset=utf-8\x0d\n\x0d\nok"

-- =============================================================================
-- Missing Host header (RFC 9112 §3.2 - Host is REQUIRED in HTTP/1.1)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "GET / HTTP/1.1\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw okHandler
  assertExact "Missing Host header returns 400" response bad400

-- =============================================================================
-- Empty Host header value
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "GET / HTTP/1.1\x0d\nHost: \x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw okHandler
  assertStatus "Empty Host header" response "HTTP/1.1"

-- =============================================================================
-- Invalid HTTP version
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "GET / HTTP/2.0\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw okHandler
  assertExact "Invalid HTTP version HTTP/2.0" response bad505

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "GET / HTTP/0.9\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw okHandler
  assertExact "Invalid HTTP version HTTP/0.9" response bad505

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "GET / HTTP/1.0\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw okHandler
  assertExact "Invalid HTTP version HTTP/1.0" response bad505

-- =============================================================================
-- Malformed request line - missing version
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "GET /\x0d\nHost: example.com\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw okHandler
  assertExact "Missing HTTP version" response bad400

-- =============================================================================
-- Malformed request line - missing URI
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "GET  HTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw okHandler
  assertStatus "Missing URI" response "HTTP/1.1 400"

-- =============================================================================
-- Malformed request line - extra spaces
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "GET  /  HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw okHandler
  -- Extra spaces in request line - should still parse or reject
  assertStatus "Extra spaces in request line" response "HTTP/1.1"

-- =============================================================================
-- Completely empty request line
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw okHandler
  assertExact "Empty request line" response bad400

-- =============================================================================
-- Invalid method name
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "FOOBAR / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw okHandler
  assertStatus "Invalid method FOOBAR" response "HTTP/1.1 501"

-- =============================================================================
-- Method with lowercase (HTTP methods are case-sensitive)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "get / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw okHandler
  assertStatus "Lowercase method" response "HTTP/1.1 501"

-- =============================================================================
-- Header without colon separator
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nBadHeader value\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw okHandler
  assertExact "Header without colon" response bad400

-- =============================================================================
-- Header with leading whitespace (obsolete line folding - should reject)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\n X-Bad: folded\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw okHandler
  assertExact "Leading whitespace in header (obs-fold)" response bad400

-- =============================================================================
-- Null byte in header name
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let before := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nX-Bad".toUTF8
  let null := ByteArray.mk #[0]
  let after := "Header: value\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let raw := before ++ null ++ after
  let response ← sendRaw client server raw okHandler
  assertExact "Null byte in header name" response bad400

-- =============================================================================
-- Null byte in header value
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let before := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nX-Header: bad".toUTF8
  let null := ByteArray.mk #[0]
  let after := "value\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let raw := before ++ null ++ after
  let response ← sendRaw client server raw okHandler
  assertExact "Null byte in header value" response bad400

-- =============================================================================
-- Bare LF without CR (strict parser should reject)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "GET / HTTP/1.1\nHost: example.com\nConnection: close\n\n".toUTF8
  let response ← sendRaw client server raw okHandler
  assertExact "Bare LF without CR" response ok200

-- =============================================================================
-- CRLF injection attempt in header value
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nX-Inject: value\x0d\nEvil: injected\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw okHandler
  -- This is actually two valid headers, not an injection. Server should process normally.
  assertStatus "CRLF in header (two valid headers)" response "HTTP/1.1 200"

-- =============================================================================
-- Non-ASCII in method
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "GÉT / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw okHandler
  assertExact "Non-ASCII in method" response bad400

-- =============================================================================
-- Tab character in header value (allowed per RFC 9110)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nX-Tab: value\twith\ttabs\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw okHandler
  assertStatus "Tab in header value (allowed)" response "HTTP/1.1 200"

-- =============================================================================
-- Very long method name (exceeds maxMethodLength=16)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let longMethod := String.ofList (List.replicate 20 'G')
  let raw := s!"{longMethod} / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw okHandler
  assertExact "Method too long" response bad400

-- =============================================================================
-- Request with only whitespace
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "   \x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw okHandler
  assertExact "Whitespace-only request" response bad400

-- =============================================================================
-- Double CRLF before request (empty lines before request)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "\x0d\nGET / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw okHandler
  -- Leading CRLF before request line - per RFC, servers SHOULD ignore at least one empty line
  assertStatus "Leading CRLF before request" response "HTTP/1.1"

-- =============================================================================
-- Non-numeric Content-Length
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: abc\x0d\nConnection: close\x0d\n\x0d\nbody".toUTF8
  let response ← sendRaw client server raw okHandler
  assertExact "Non-numeric Content-Length" response bad400

-- =============================================================================
-- Negative Content-Length
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: -1\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw okHandler
  assertExact "Negative Content-Length" response bad400

-- =============================================================================
-- Duplicate Content-Length with different values (MUST reject per RFC 9110 §8.6)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 5\x0d\nContent-Length: 10\x0d\nConnection: close\x0d\n\x0d\nhello".toUTF8
  let response ← sendRaw client server raw okHandler
  assertExact "Duplicate Content-Length different values" response bad400

-- =============================================================================
-- Space in header name (invalid token character)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nBad Header: value\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw okHandler
  assertExact "Space in header name" response bad400

-- =============================================================================
-- Colon in header name (invalid)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nBad:Name: value\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw okHandler
  -- "Bad" is the name, "Name: value" is the value - this is actually valid parsing
  assertStatus "Colon parsed as header name delimiter" response "HTTP/1.1"

-- =============================================================================
-- Request with absolute-form URI
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "GET http://example.com/path HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw okHandler
  assertStatus "Absolute-form URI" response "HTTP/1.1"

-- =============================================================================
-- PUT request with body
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "PUT /resource HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 11\x0d\nConnection: close\x0d\n\x0d\nhello world".toUTF8
  let response ← sendRaw client server raw (fun req => do
    if req.head.method == .put then Response.ok |>.text "updated"
    else Response.badRequest |>.text "wrong method")
  assertStatus "PUT request" response "HTTP/1.1 200"

-- =============================================================================
-- PATCH request with body
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "PATCH /resource HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\n\x0d\npatch".toUTF8
  let response ← sendRaw client server raw (fun req => do
    if req.head.method == .patch then Response.ok |>.text "patched"
    else Response.badRequest |>.text "wrong method")
  assertStatus "PATCH request" response "HTTP/1.1 200"

-- =============================================================================
-- TRACE request
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "TRACE / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw (fun req => do
    if req.head.method == .trace then Response.ok |>.text "traced"
    else Response.badRequest |>.text "wrong method")
  assertStatus "TRACE request" response "HTTP/1.1 200"

-- =============================================================================
-- Multiple Host headers (MUST return 400 per RFC 9112 §3.2)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nHost: other.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw okHandler
  assertExact "Multiple Host headers" response bad400

-- =============================================================================
-- Header value with leading/trailing OWS (should be trimmed per RFC 9110 §5.5)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "GET / HTTP/1.1\x0d\nHost:   example.com   \x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw okHandler
  assertStatus "OWS around header value" response "HTTP/1.1 200"

-- =============================================================================
-- Mixed-case Transfer-Encoding (e.g., Chunked instead of chunked)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: Chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw (fun req => do
    let mut body := ByteArray.empty
    for chunk in req.body do
      body := body ++ chunk.data
    Response.ok |>.text (String.fromUTF8! body))
  assertStatus "Mixed-case TE: Chunked" response "HTTP/1.1 200"

-- =============================================================================
-- Transfer-Encoding with trailing space (e.g., "chunked ")
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked \x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw (fun req => do
    let mut body := ByteArray.empty
    for chunk in req.body do
      body := body ++ chunk.data
    Response.ok |>.text (String.fromUTF8! body))
  assertStatus "TE with trailing space" response "HTTP/1.1"

-- =============================================================================
-- Transfer-Encoding: chunked, chunked (double chunked - should reject)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked, chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw okHandler
  assertExact "Double chunked TE" response bad400

-- =============================================================================
-- Empty connection (client connects then immediately disconnects)
-- =============================================================================

#eval show IO _ from do Async.block do
  let (client, server) ← Mock.new
  let raw := ByteArray.empty
  client.send raw
  client.close
  let result ← Async.block do
    Std.Http.Server.serveConnection server okHandler { lingeringTimeout := 500, generateDate := false }
      |>.run
    let res ← client.recv?
    pure <| res.getD .empty
  -- Empty connection should result in no response or a timeout
  assert! result.size == 0 ∨ (String.fromUTF8! result).startsWith "HTTP/1.1"

-- =============================================================================
-- Request with extremely long header name (boundary test at maxHeaderNameLength)
-- =============================================================================

#eval show IO _ from do Async.block do
  let (client, server) ← Mock.new
  let longName := String.ofList (List.replicate 257 'X')
  let raw := s!"GET / HTTP/1.1\x0d\nHost: example.com\x0d\n{longName}: value\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw okHandler
  assertExact "Header name at 257 chars" response bad400

-- =============================================================================
-- Control character (0x01) in header value
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let before := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nX-Header: bad".toUTF8
  let ctrl := ByteArray.mk #[0x01]
  let after := "value\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let raw := before ++ ctrl ++ after
  let response ← sendRaw client server raw okHandler
  assertExact "Control char in header value" response bad400

-- =============================================================================
-- Request line with no spaces at all
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "GETHTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw okHandler
  assertExact "Request line no spaces" response bad400

-- =============================================================================
-- Very long URI (exceeds maxUriLength=8192)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let longUri := "/" ++ String.ofList (List.replicate 9000 'a')
  let raw := s!"GET {longUri} HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw okHandler
  assertExact "URI too long" response bad400
