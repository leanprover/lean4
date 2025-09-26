import Std.Internal.Http.Protocol.H1.Parser

open Std.Http.Protocol

def runParser (parser : Std.Internal.Parsec.ByteArray.Parser α) (s : String) : IO α :=
  IO.ofExcept (parser.run s.toUTF8)

-- Chunk parsing tests
/--
info: 16 / #[] / "adasdssdabcdabde"
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser H1.parseChunk "10\r\nadasdssdabcdabde"
  match result with
  | some (size, ext, body) => IO.println s!"{size} / {ext} / {String.fromUTF8! body.toByteArray |>.quote}"
  | none => IO.println "end chunk"

/--
info: end chunk
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser H1.parseChunk "0\r\n"
  match result with
  | some (size, ext, body) => IO.println s!"{size} / {ext} / {String.fromUTF8! body.toByteArray |>.quote}"
  | none => IO.println "end chunk"

/--
info: 255 / #[] / "This is a test chunk with exactly 255 bytes of data. Lorem ipsum dolor sit amet, consectetur adipiscing elit. Sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris lorem ipsu."
-/
#guard_msgs in
#eval show IO _ from do
  let testData := "This is a test chunk with exactly 255 bytes of data. Lorem ipsum dolor sit amet, consectetur adipiscing elit. Sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris lorem ipsu."
  let result ← runParser H1.parseChunk s!"FF\r\n{testData}"
  match result with
  | some (size, ext, body) => IO.println s!"{size} / {ext} / {String.fromUTF8! body.toByteArray |>.quote}"
  | none => IO.println "end chunk"

-- Chunk size parsing tests (refactored to use runParser)
/--
info: 16 / #[(abc, none), (def, none), (g, (some h))]
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Protocol.H1.parseChunkSize "10;abc;def;g=h\r\n"
  IO.println s!"{result.1} / {result.2}"

/--
info: 0 / #[(abc, none), (def, none), (g, (some h))]
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Protocol.H1.parseChunkSize "0;abc;def;g=h\r\n"
  IO.println s!"{result.1} / {result.2}"

/--
info: 4095 / #[]
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Protocol.H1.parseChunkSize "FFF\r\n"
  IO.println s!"{result.1} / {result.2}"

/--
info: 1 / #[(name, (some (value with spaces)))]
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Protocol.H1.parseChunkSize "1;name=\"value with spaces\"\r\n"
  IO.println s!"{result.1} / {result.2}"

-- Single header parsing tests (refactored to use runParser)
/--
info: User-Agent / "Mozilla/5.0 (X11; Linux x86_64; rv:143.0) Gecko/20100101 Firefox/143.0"
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (Std.Http.Protocol.H1.parseSingleHeader 256) "User-Agent: Mozilla/5.0 (X11; Linux x86_64; rv:143.0) Gecko/20100101 Firefox/143.0\r\n"
  match result with
  | some (k, v) => IO.println s!"{k} / {v.quote}"
  | none => IO.println "end"

/--
info: Content-Type / "application/json; charset=utf-8"
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (Std.Http.Protocol.H1.parseSingleHeader 256) "Content-Type: application/json; charset=utf-8\r\n"
  match result with
  | some (k, v) => IO.println s!"{k} / {v.quote}"
  | none => IO.println "end"

/--
info: Authorization / Bearer eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (Std.Http.Protocol.H1.parseSingleHeader 256) "Authorization: Bearer eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9\r\n"
  match result with
  | some (k, v) => IO.println s!"{k} / {v}"
  | none => IO.println "end"

/--
info: end
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (Std.Http.Protocol.H1.parseSingleHeader 256) "\r\n"
  match result with
  | some (k, v) => IO.println s!"{k} / {v}"
  | none => IO.println "end"

/--
error: offset 0: unexpected end of input
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (Std.Http.Protocol.H1.parseTrailers 256) ""
  IO.println s!"{result}"

/--
info: #[]
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (Std.Http.Protocol.H1.parseTrailers 256) "\r\n"
  IO.println s!"{result}"

/--
info: #[(X-Checksum, abc123), (X-Timestamp, 2023-01-01T12:00:00Z)]
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (Std.Http.Protocol.H1.parseTrailers 256) "X-Checksum: abc123\r\nX-Timestamp: 2023-01-01T12:00:00Z\r\n\r\n"
  IO.println s!"{result}"

-- Request line parsing tests (refactored to use runParser)
/--
info: Std.Http.Method.get / Std.Http.RequestTarget.originForm { segments := #["ata", ""], absolute := true } none / Std.Http.Version.v11
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Protocol.H1.parseRequestLine "GET /ata/ HTTP/1.1\r\n"
  IO.println s!"{repr result.method} / {repr result.uri} / {repr result.version}"

/--
info: Std.Http.Method.post / Std.Http.RequestTarget.originForm { segments := #["api", "v1", "users"], absolute := true } none / Std.Http.Version.v11
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Protocol.H1.parseRequestLine "POST /api/v1/users HTTP/1.1\r\n"
  IO.println s!"{repr result.method} / {repr result.uri} / {repr result.version}"

/--
info: Std.Http.Method.put / Std.Http.RequestTarget.originForm
  { segments := #["data"], absolute := true }
  (some #[("param1", some "value1"), ("param2", some "value2")]) / Std.Http.Version.v11
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Protocol.H1.parseRequestLine "PUT /data?param1=value1&param2=value2 HTTP/1.1\r\n"
  IO.println s!"{repr result.method} / {repr result.uri} / {repr result.version}"

/--
info: Std.Http.Method.delete / Std.Http.RequestTarget.originForm { segments := #["items", "123"], absolute := true } none / Std.Http.Version.v11
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Protocol.H1.parseRequestLine "DELETE /items/123 HTTP/1.1\r\n"
  IO.println s!"{repr result.method} / {repr result.uri} / {repr result.version}"

/--
info: Std.Http.Method.head / Std.Http.RequestTarget.originForm { segments := #[], absolute := true } none / Std.Http.Version.v11
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Protocol.H1.parseRequestLine "HEAD / HTTP/1.1\r\n"
  IO.println s!"{repr result.method} / {repr result.uri} / {repr result.version}"

/--
info: Std.Http.Method.options / Std.Http.RequestTarget.asteriskForm / Std.Http.Version.v11
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Protocol.H1.parseRequestLine "OPTIONS * HTTP/1.1\r\n"
  IO.println s!"{repr result.method} / {repr result.uri} / {repr result.version}"

-- Additional edge case tests
/--
info: 0 / #[]
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Protocol.H1.parseChunkSize "0\r\n"
  IO.println s!"{result.1} / {result.2}"

/--
info: X-Custom-Header / value with multiple   spaces
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser (Std.Http.Protocol.H1.parseSingleHeader 256) "X-Custom-Header: value with multiple   spaces\r\n"
  match result with
  | some (k, v) => IO.println s!"{k} / {v}"
  | none => IO.println "end"
