import Std.Internal.Http
import Std.Internal.Async
import Std.Internal.Async.Timer

open Std.Internal.IO Async
open Std Http

abbrev TestHandler := Request Body.Stream → ContextAsync (Response Body.Stream)

instance : Std.Http.Server.Handler TestHandler where
  onRequest handler request := handler request

open Std.Http.Internal

/-!
# HTTP Trailer Tests

Tests for HTTP/1.1 chunked transfer encoding trailers (RFC 9112 §7.1.2).
Covers: basic trailer parsing, empty trailers, limit enforcement, malformed trailers,
and potential parser abuse scenarios.
-/

/-- Send raw bytes to the server and return the response. -/
def sendRaw (client : Mock.Client) (server : Mock.Server) (raw : ByteArray)
    (handler : Request Body.Stream → ContextAsync (Response Body.Stream))
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

def bodyHandler : Request Body.Stream → ContextAsync (Response Body.Stream) :=
  fun req => do
    let mut body := ByteArray.empty
    for chunk in req.body do
      body := body ++ chunk.data
    Response.ok |>.text (String.fromUTF8! body)

def bad400 : String :=
  "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"

-- =============================================================================
-- Chunked body with no trailers (just terminal chunk + empty line)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw bodyHandler
  assertStatus "Chunked no trailers" response "HTTP/1.1 200"

-- =============================================================================
-- Chunked body with a single trailer header
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\nChecksum: abc123\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw bodyHandler
  assertStatus "Single trailer header" response "HTTP/1.1 200"

-- =============================================================================
-- Chunked body with multiple trailer headers
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\nChecksum: abc123\x0d\nExpires: Thu, 01 Dec 1994 16:00:00 GMT\x0d\nX-Custom: value\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw bodyHandler
  assertStatus "Multiple trailer headers" response "HTTP/1.1 200"

-- =============================================================================
-- Chunked body with trailer having long value (within default limit of 8192)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let longValue := String.ofList (List.replicate 8000 'v')
  let raw := s!"POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nabc\x0d\n0\x0d\nX-Long: {longValue}\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw bodyHandler
  assertStatus "Trailer with long value (8000 chars)" response "HTTP/1.1 200"

-- =============================================================================
-- Chunked body with trailer value exceeding maxHeaderValueLength (8192)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let longValue := String.ofList (List.replicate 8193 'v')
  let raw := s!"POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nabc\x0d\n0\x0d\nX-Long: {longValue}\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw bodyHandler
  assertExact "Trailer value exceeds limit" response bad400

-- =============================================================================
-- Chunked body with trailer name exceeding maxHeaderNameLength (256)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let longName := String.ofList (List.replicate 257 'X')
  let raw := s!"POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nabc\x0d\n0\x0d\n{longName}: value\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw bodyHandler
  assertExact "Trailer name exceeds limit" response bad400

-- =============================================================================
-- Exceed maxTrailerHeaders limit (default 100)
-- Use a reduced limit to keep the test fast.
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  -- Use a config with maxTrailerHeaders = 3 to keep test small
  let config : Config := { lingeringTimeout := 3000, maxTrailerHeaders := 3, generateDate := false }
  let trailers := "T1: v1\x0d\nT2: v2\x0d\nT3: v3\x0d\nT4: v4\x0d\n"
  let raw := s!"POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nabc\x0d\n0\x0d\n{trailers}\x0d\n".toUTF8
  let response ← sendRaw client server raw bodyHandler (config := config)
  assertExact "Too many trailer headers (4 > 3)" response bad400

-- =============================================================================
-- Trailer count exactly at the limit should succeed
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let config : Config := { lingeringTimeout := 3000, maxTrailerHeaders := 3, generateDate := false }
  let trailers := "T1: v1\x0d\nT2: v2\x0d\nT3: v3\x0d\n"
  let raw := s!"POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nabc\x0d\n0\x0d\n{trailers}\x0d\n".toUTF8
  let response ← sendRaw client server raw bodyHandler (config := config)
  assertStatus "Trailer count exactly at limit (3)" response "HTTP/1.1 200"

-- =============================================================================
-- Trailer with null byte in name
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let before := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nabc\x0d\n0\x0d\nX-Bad".toUTF8
  let null := ByteArray.mk #[0]
  let after := "Name: value\x0d\n\x0d\n".toUTF8
  let raw := before ++ null ++ after
  let response ← sendRaw client server raw bodyHandler
  assertExact "Null byte in trailer name" response bad400

-- =============================================================================
-- Trailer with null byte in value
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let before := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nabc\x0d\n0\x0d\nX-Header: bad".toUTF8
  let null := ByteArray.mk #[0]
  let after := "value\x0d\n\x0d\n".toUTF8
  let raw := before ++ null ++ after
  let response ← sendRaw client server raw bodyHandler
  assertExact "Null byte in trailer value" response bad400

-- =============================================================================
-- Trailer with control character (0x01) in value
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let before := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nabc\x0d\n0\x0d\nX-Header: bad".toUTF8
  let ctrl := ByteArray.mk #[0x01]
  let after := "value\x0d\n\x0d\n".toUTF8
  let raw := before ++ ctrl ++ after
  let response ← sendRaw client server raw bodyHandler
  assertExact "Control char in trailer value" response bad400

-- =============================================================================
-- Trailer without colon separator (malformed field line)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nabc\x0d\n0\x0d\nBadTrailer value\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw bodyHandler
  assertExact "Trailer without colon" response bad400

-- =============================================================================
-- Trailer with leading whitespace (obsolete line folding)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nabc\x0d\n0\x0d\n X-Bad: folded\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw bodyHandler
  assertExact "Leading whitespace in trailer (obs-fold)" response bad400

-- =============================================================================
-- Trailer with space in name (invalid token character)
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nabc\x0d\n0\x0d\nBad Name: value\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw bodyHandler
  assertExact "Space in trailer name" response bad400

-- =============================================================================
-- Multiple chunks followed by trailers
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n6\x0d\n world\x0d\n0\x0d\nChecksum: deadbeef\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw bodyHandler
  assertStatus "Multiple chunks then trailers" response "HTTP/1.1 200"

-- =============================================================================
-- Terminal chunk with extensions followed by trailers
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0;ext=val\x0d\nX-Trailer: yes\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw bodyHandler
  assertStatus "Terminal chunk ext + trailers" response "HTTP/1.1 200"

-- =============================================================================
-- Missing final CRLF after trailers (incomplete message)
-- The server should either reject or timeout waiting for more data.
-- =============================================================================

#eval show IO _ from Async.block do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nabc\x0d\n0\x0d\nX-Trailer: value\x0d\n".toUTF8
  client.send raw
  client.close
  let result ← Async.block do
    Std.Http.Server.serveConnection server bodyHandler { lingeringTimeout := 500, generateDate := false }
      |>.run
    let res ← client.recv?
    pure <| res.getD .empty
  -- Incomplete trailer section: server should return 400 or empty response
  let responseStr := String.fromUTF8! result
  assert! result.size == 0 ∨ responseStr.startsWith "HTTP/1.1 400"

-- =============================================================================
-- Trailer encoding round-trip test
-- =============================================================================

#eval show IO _ from Async.block do
  let trailer := Trailer.empty
    |>.header "Checksum" "abc123"
    |>.header "Expires" "Thu, 01 Dec 1994"
  let encoded := (Encode.encode (v := .v11) ChunkedBuffer.empty trailer).toByteArray
  let s := String.fromUTF8! encoded
  -- Should contain terminal chunk "0\r\n", trailer fields, and final "\r\n"
  assert! s.contains "0\x0d\n"
  assert! s.contains "Checksum: abc123\x0d\n"
  assert! s.contains "Expires: Thu, 01 Dec 1994\x0d\n"

-- =============================================================================
-- Empty trailer encoding
-- =============================================================================

#eval show IO _ from Async.block do
  let trailer := Trailer.empty
  let encoded := (Encode.encode (v := .v11) ChunkedBuffer.empty trailer).toByteArray
  let s := String.fromUTF8! encoded
  -- Should be just "0\r\n\r\n"
  assert! s == "0\x0d\n\x0d\n"

-- =============================================================================
-- maxTrailerHeaders = 0 means no trailers allowed
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let config : Config := { lingeringTimeout := 3000, maxTrailerHeaders := 0, generateDate := false }
  -- Even a single trailer should be rejected
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nabc\x0d\n0\x0d\nX-Trailer: rejected\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw bodyHandler (config := config)
  assertExact "maxTrailerHeaders=0 rejects any trailer" response bad400

-- =============================================================================
-- maxTrailerHeaders = 0 but no trailers present should succeed
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let config : Config := { lingeringTimeout := 3000, maxTrailerHeaders := 0, generateDate := false }
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nabc\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw bodyHandler (config := config)
  assertStatus "maxTrailerHeaders=0 with no trailers" response "HTTP/1.1 200"

-- =============================================================================
-- Trailer with very long name at exactly the limit (256 chars) should succeed
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let exactName := String.ofList (List.replicate 256 'X')
  let raw := s!"POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nabc\x0d\n0\x0d\n{exactName}: value\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw bodyHandler
  assertStatus "Trailer name at exactly 256 chars" response "HTTP/1.1 200"

-- =============================================================================
-- Trailer with value at exactly the limit (8192 chars) should succeed
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let exactValue := String.ofList (List.replicate 8192 'v')
  let raw := s!"POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nabc\x0d\n0\x0d\nX-Exact: {exactValue}\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw bodyHandler
  assertStatus "Trailer value at exactly 8192 chars" response "HTTP/1.1 200"

-- =============================================================================
-- Many trailers at a reduced limit with varied field sizes
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let config : Config := { lingeringTimeout := 3000, maxTrailerHeaders := 5, maxHeaderValueLength := 50, generateDate := false }
  -- 5 trailers with values near the limit
  let longVal := String.ofList (List.replicate 50 'z')
  let trailers := s!"T1: {longVal}\x0d\nT2: {longVal}\x0d\nT3: {longVal}\x0d\nT4: {longVal}\x0d\nT5: {longVal}\x0d\n"
  let raw := s!"POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nabc\x0d\n0\x0d\n{trailers}\x0d\n".toUTF8
  let response ← sendRaw client server raw bodyHandler (config := config)
  assertStatus "5 trailers at limit with long values" response "HTTP/1.1 200"

-- =============================================================================
-- Many trailers exceed reduced limit with large values
-- =============================================================================

#eval show IO _ from do
  let (client, server) ← Mock.new
  let config : Config := { lingeringTimeout := 3000, maxTrailerHeaders := 5, maxHeaderValueLength := 50, generateDate := false }
  let longVal := String.ofList (List.replicate 51 'z')
  let raw := s!"POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nabc\x0d\n0\x0d\nT1: {longVal}\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw bodyHandler (config := config)
  assertExact "Trailer value exceeds reduced limit (51 > 50)" response bad400
