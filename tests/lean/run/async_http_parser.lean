/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
import Std.Internal.Http.Protocol.H1.Parser

open Std.Http.Protocol

/-!
# HTTP/1.1 Parser Tests

Comprehensive tests for H1 protocol parsing including chunks, headers,
request lines, status lines, and edge cases.
-/

def runParser (parser : Std.Internal.Parsec.ByteArray.Parser α) (s : String) : IO α :=
  IO.ofExcept (parser.run s.toUTF8)

-- ============================================================================
-- Chunk Parsing Tests
-- ============================================================================

/--
info: 16 / #[] / "adasdssdabcdabde"
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseChunk {}) "10\r\nadasdssdabcdabde"
  match result with
  | some (size, ext, body) => IO.println s!"{size} / {ext} / {String.fromUTF8! body.toByteArray |>.quote}"
  | none => IO.println "end chunk"

/--
info: end chunk
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseChunk {}) "0\r\n"
  match result with
  | some (size, ext, body) => IO.println s!"{size} / {ext} / {String.fromUTF8! body.toByteArray |>.quote}"
  | none => IO.println "end chunk"

/--
info: 255 / #[] / "This is a test chunk with exactly 255 bytes of data. Lorem ipsum dolor sit amet, consectetur adipiscing elit. Sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris lorem ipsu."
-/
#guard_msgs in
#eval show IO _ from do
  let testData := "This is a test chunk with exactly 255 bytes of data. Lorem ipsum dolor sit amet, consectetur adipiscing elit. Sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris lorem ipsu."
  let result ← runParser (H1.parseChunk {}) s!"FF\r\n{testData}"
  match result with
  | some (size, ext, body) => IO.println s!"{size} / {ext} / {String.fromUTF8! body.toByteArray |>.quote}"
  | none => IO.println "end chunk"

-- ============================================================================
-- Chunk Size Parsing Tests
-- ============================================================================

/--
info: 16 / #[(abc, none), (def, none), (g, (some h))]
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseChunkSize {}) "10;abc;def;g=h\r\n"
  IO.println s!"{result.1} / {result.2}"

/--
info: 0 / #[(abc, none), (def, none), (g, (some h))]
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseChunkSize {}) "0;abc;def;g=h\r\n"
  IO.println s!"{result.1} / {result.2}"

/--
info: 4095 / #[]
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseChunkSize {}) "FFF\r\n"
  IO.println s!"{result.1} / {result.2}"

/--
info: 1 / #[(name, (some (value with spaces)))]
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseChunkSize {}) "1;name=\"value with spaces\"\r\n"
  IO.println s!"{result.1} / {result.2}"

/--
info: 0 / #[]
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseChunkSize {}) "0\r\n"
  IO.println s!"{result.1} / {result.2}"

/--
info: 16 / #[]
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseChunkSize {}) "10\r\n"
  IO.println s!"{result.1} / {result.2}"

/--
info: 255 / #[]
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseChunkSize {}) "FF\r\n"
  IO.println s!"{result.1} / {result.2}"

/--
info: 255 / #[]
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseChunkSize {}) "ff\r\n"
  IO.println s!"{result.1} / {result.2}"

-- ============================================================================
-- Chunk Extension Tests
-- ============================================================================

/--
info: 10 / #[(ext1, none)]
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseChunkSize {}) "A;ext1\r\n"
  IO.println s!"{result.1} / {result.2}"

/--
info: 10 / #[(name, (some value))]
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseChunkSize {}) "A;name=value\r\n"
  IO.println s!"{result.1} / {result.2}"

/--
info: 10 / #[(name, (some (value with spaces)))]
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseChunkSize {}) "A;name=\"value with spaces\"\r\n"
  IO.println s!"{result.1} / {result.2}"

-- ============================================================================
-- Single Header Parsing Tests
-- ============================================================================

/--
info: User-Agent / "Mozilla/5.0 (X11; Linux x86_64; rv:143.0) Gecko/20100101 Firefox/143.0"
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseSingleHeader {}) "User-Agent: Mozilla/5.0 (X11; Linux x86_64; rv:143.0) Gecko/20100101 Firefox/143.0\r\n"
  match result with
  | some (k, v) => IO.println s!"{k} / {v.quote}"
  | none => IO.println "end"

/--
info: Content-Type / "application/json; charset=utf-8"
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseSingleHeader {}) "Content-Type: application/json; charset=utf-8\r\n"
  match result with
  | some (k, v) => IO.println s!"{k} / {v.quote}"
  | none => IO.println "end"

/--
info: Authorization / Bearer eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseSingleHeader {}) "Authorization: Bearer eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9\r\n"
  match result with
  | some (k, v) => IO.println s!"{k} / {v}"
  | none => IO.println "end"

/--
info: end
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseSingleHeader {}) "\r\n"
  match result with
  | some (k, v) => IO.println s!"{k} / {v}"
  | none => IO.println "end"

/--
info: X-Custom-Header / value with multiple   spaces
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseSingleHeader {}) "X-Custom-Header: value with multiple   spaces\r\n"
  match result with
  | some (k, v) => IO.println s!"{k} / {v}"
  | none => IO.println "end"

/--
info: Valid-Name / value
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseSingleHeader {}) "Valid-Name: value\r\n"
  match result with
  | some (k, v) => IO.println s!"{k} / {v}"
  | none => IO.println "end"

/--
info: X-Custom-123 / test
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseSingleHeader {}) "X-Custom-123: test\r\n"
  match result with
  | some (k, v) => IO.println s!"{k} / {v}"
  | none => IO.println "end"

/--
info: X-Special / value with spaces and !@#$%^&*()
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseSingleHeader {}) "X-Special: value with spaces and !@#$%^&*()\r\n"
  match result with
  | some (k, v) => IO.println s!"{k} / {v}"
  | none => IO.println "end"

-- ============================================================================
-- Header Edge Cases
-- ============================================================================

-- Empty header value requires at least one character and fails
/--
error: offset 8: expected at least one char
-/
#guard_msgs in
#eval show IO _ from do
  let _ ← runParser (H1.parseSingleHeader {}) "X-Empty:\r\n"
  IO.println "should not reach"

-- Tab character is preserved in header value
/--
info: X-Tab / "\t"
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseSingleHeader {}) "X-Tab:\t\r\n"
  match result with
  | some (k, v) => IO.println s!"{k} / {v.quote}"
  | none => IO.println "end"

-- Long header values (near limit of 8192)
/--
info: X-Long / 8000 chars
-/
#guard_msgs in
#eval show IO _ from do
  let longValue := String.ofList (List.replicate 8000 'x')
  let result ← runParser (H1.parseSingleHeader {}) s!"X-Long: {longValue}\r\n"
  match result with
  | some (k, v) => IO.println s!"{k} / {v.length} chars"
  | none => IO.println "end"

-- ============================================================================
-- Trailer Parsing Tests
-- ============================================================================

/--
error: offset 0: unexpected end of input
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseTrailers {}) ""
  IO.println s!"{result}"

/--
info: #[]
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseTrailers {}) "\r\n"
  IO.println s!"{result}"

/--
info: #[(X-Checksum, abc123), (X-Timestamp, 2023-01-01T12:00:00Z)]
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseTrailers {}) "X-Checksum: abc123\r\nX-Timestamp: 2023-01-01T12:00:00Z\r\n\r\n"
  IO.println s!"{result}"

/--
info: #[(X-Checksum, abc123)]
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseTrailers {}) "X-Checksum: abc123\r\n\r\n"
  IO.println s!"{result}"

/--
info: #[(X-First, value1), (X-Second, value2)]
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseTrailers {}) "X-First: value1\r\nX-Second: value2\r\n\r\n"
  IO.println s!"{result}"

-- ============================================================================
-- Request Line Parsing Tests
-- ============================================================================

/--
info: Std.Http.Method.get / Std.Http.RequestTarget.originForm { segments := #["ata", ""], absolute := true } none none / Std.Http.Version.v11
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseRequestLine {}) "GET /ata/ HTTP/1.1\r\n"
  IO.println s!"{repr result.method} / {repr result.uri} / {repr result.version}"

/--
info: Std.Http.Method.post / Std.Http.RequestTarget.originForm { segments := #["api", "v1", "users"], absolute := true } none none / Std.Http.Version.v11
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseRequestLine {}) "POST /api/v1/users HTTP/1.1\r\n"
  IO.println s!"{repr result.method} / {repr result.uri} / {repr result.version}"

/--
info: Std.Http.Method.put / Std.Http.RequestTarget.originForm
  { segments := #["data"], absolute := true }
  (some #[("param1", some "value1"), ("param2", some "value2")])
  none / Std.Http.Version.v11
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseRequestLine {}) "PUT /data?param1=value1&param2=value2 HTTP/1.1\r\n"
  IO.println s!"{repr result.method} / {repr result.uri} / {repr result.version}"

/--
info: Std.Http.Method.delete / Std.Http.RequestTarget.originForm { segments := #["items", "123"], absolute := true } none none / Std.Http.Version.v11
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseRequestLine {}) "DELETE /items/123 HTTP/1.1\r\n"
  IO.println s!"{repr result.method} / {repr result.uri} / {repr result.version}"

/--
info: Std.Http.Method.head / Std.Http.RequestTarget.originForm { segments := #[], absolute := true } none none / Std.Http.Version.v11
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseRequestLine {}) "HEAD / HTTP/1.1\r\n"
  IO.println s!"{repr result.method} / {repr result.uri} / {repr result.version}"

/--
info: Std.Http.Method.options / Std.Http.RequestTarget.asteriskForm / Std.Http.Version.v11
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseRequestLine {}) "OPTIONS * HTTP/1.1\r\n"
  IO.println s!"{repr result.method} / {repr result.uri} / {repr result.version}"

/--
info: Std.Http.Method.get / Std.Http.Version.v11
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseRequestLine {}) "GET / HTTP/1.1\r\n"
  IO.println s!"{repr result.method} / {repr result.version}"

-- ============================================================================
-- All Standard HTTP Methods
-- ============================================================================

/--
info: Std.Http.Method.head
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseRequestLine {}) "HEAD / HTTP/1.1\r\n"
  IO.println s!"{repr result.method}"

/--
info: Std.Http.Method.put
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseRequestLine {}) "PUT /resource HTTP/1.1\r\n"
  IO.println s!"{repr result.method}"

/--
info: Std.Http.Method.patch
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseRequestLine {}) "PATCH /resource HTTP/1.1\r\n"
  IO.println s!"{repr result.method}"

/--
info: Std.Http.Method.options
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseRequestLine {}) "OPTIONS * HTTP/1.1\r\n"
  IO.println s!"{repr result.method}"

/--
info: Std.Http.Method.trace
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseRequestLine {}) "TRACE / HTTP/1.1\r\n"
  IO.println s!"{repr result.method}"

/--
info: Std.Http.Method.connect
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseRequestLine {}) "CONNECT example.com:443 HTTP/1.1\r\n"
  IO.println s!"{repr result.method}"

-- ============================================================================
-- Invalid HTTP Versions
-- ============================================================================

/--
error: offset 14: expected value but got none
-/
#guard_msgs in
#eval show IO _ from do
  let _ ← runParser (H1.parseRequestLine {}) "GET / HTTP/1.0\r\n"
  IO.println "should not reach"

/--
info: Std.Http.Method.get / Std.Http.Version.v20
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseRequestLine {}) "GET / HTTP/2.0\r\n"
  IO.println s!"{repr result.method} / {repr result.version}"

/--
error: offset 14: expected value but got none
-/
#guard_msgs in
#eval show IO _ from do
  let _ ← runParser (H1.parseRequestLine {}) "GET / HTTP/3.1\r\n"
  IO.println "should not reach"

-- ============================================================================
-- Case-Sensitive Method Names
-- ============================================================================

/--
error: offset 0: expected: '80'
-/
#guard_msgs in
#eval show IO _ from do
  let _ ← runParser (H1.parseRequestLine {}) "get / HTTP/1.1\r\n"
  IO.println "should not reach"

/--
error: offset 1: expected: '69'
-/
#guard_msgs in
#eval show IO _ from do
  let _ ← runParser (H1.parseRequestLine {}) "Get / HTTP/1.1\r\n"
  IO.println "should not reach"

/--
error: offset 1: expected: '65'
-/
#guard_msgs in
#eval show IO _ from do
  let _ ← runParser (H1.parseRequestLine {}) "Post / HTTP/1.1\r\n"
  IO.println "should not reach"

-- ============================================================================
-- Status Line Parsing Tests
-- ============================================================================

/--
info: Std.Http.Status.ok / Std.Http.Version.v11
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseStatusLine {}) "HTTP/1.1 200 OK\r\n"
  IO.println s!"{repr result.status} / {repr result.version}"

/--
info: Std.Http.Status.notFound / Std.Http.Version.v11
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseStatusLine {}) "HTTP/1.1 404 Not Found\r\n"
  IO.println s!"{repr result.status} / {repr result.version}"

/--
info: Std.Http.Status.internalServerError / Std.Http.Version.v11
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (H1.parseStatusLine {}) "HTTP/1.1 500 Internal Server Error\r\n"
  IO.println s!"{repr result.status} / {repr result.version}"
