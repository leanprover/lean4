import Std.Http

open Std Http
open Std.Http.Protocol.H1

/-!
Tests that reading a message one byte per read gives, after every byte, the same answer as reading
the bytes so far in one read. While a line arrives in pieces the reader parses it again only when a
byte may do more than continue it (`LineScan`), so these inputs walk every part of every kind of
line: a method, a request-target and its URI check, the version, a status code and reason phrase, a
field name, the whitespace and value after it, an obs-fold line, a chunk size, chunk-extension names
and values, quoted values and their escapes, and the limits of each. Small limits keep the lines
short.
-/

def check (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw (IO.userError msg)

/-- Runs the machine until it stops making progress, collecting its output. -/
def settle (m : Machine dir) (out : ByteArray) : Machine dir × ByteArray := Id.run do
  let mut m := m
  let mut out := out
  for _ in [0:8] do
    let (m', r) := m.step
    m := m'
    out := out ++ r.output.toByteArray
    while m.canPullBody do
      let (m', chunk?) := m.pullBody
      m := m'
      if chunk?.isNone then break
  (m, out)

def small : Protocol.H1.Config :=
  { maxHeaderNameLength := 8, maxHeaderValueLength := 12, maxSpaceSequence := 3, maxUriLength := 12,
    maxReasonPhraseLength := 6, maxChunkExtNameLength := 4, maxChunkExtValueLength := 5,
    maxChunkExtensions := 2 }

/-- The error and output after feeding `input` to a server as the reads `parts`. -/
def server (parts : Array ByteArray) : Option Error × String := Id.run do
  let mut m : Machine .receiving := { config := small }
  let mut out := ByteArray.empty
  for p in parts do
    (m, out) := settle (m.feed p) out
  (m.error, String.fromUTF8Lossy out)

/-- The error and whether the response was read after sending a GET or HEAD and feeding `parts`. -/
def client (method : Method) (parts : Array ByteArray) : Option Error × Bool := Id.run do
  let mut m : Machine .sending := ({ config := small } : Machine .sending).send
    { method, version := .v11, uri := RequestTarget.originForm! "/",
      headers := Headers.empty.insert! "Host" "a" } |>.userClosedBody
  let mut out := ByteArray.empty
  let mut done := false
  for p in parts do
    (m, out) := settle (m.feed p) out
    done := done || m.isReaderComplete || m.isReaderClosed
  (m.error, done)

def bytes (s : String) : Array ByteArray :=
  s.toUTF8.toList.toArray.map fun b => ByteArray.mk #[b]

/-- After every byte of `input`, reading byte by byte answers as reading the prefix at once. -/
def sameAsWhole (who : String) (run : Array ByteArray → α) [BEq α] [Repr α] (input : String) :
    IO Unit := do
  let parts := bytes input
  for i in [1:parts.size + 1] do
    let drip := run (parts.extract 0 i)
    let whole := run #[parts.extract 0 i |>.foldl (· ++ ·) .empty]
    check (drip == whole)
      s!"{who} {input.quote}: after {i} bytes, one byte per read gives {repr drip}, one read gives {repr whole}"

/-- Runs every case and throws once, listing the failures. -/
def runCases (cases : List (IO Unit)) : IO Unit := do
  let mut errors : Array String := #[]
  for c in cases do
    try c catch e => errors := errors.push (toString e)
  unless errors.isEmpty do throw (IO.userError ("\n".intercalate errors.toList))

def head (field : String) : String := s!"GET / HTTP/1.1\r\nHost: a\r\n{field}\r\n\r\n"

def chunked (line : String) : String :=
  s!"POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n{line}\r\nhello\r\n0\r\n\r\n"

#eval runCases <| [
    -- Request lines: methods, targets, the URI check at the SP, versions, empty lines before.
    "GET /a?b=c HTTP/1.1\r\nHost: a\r\n\r\n", "\r\n\r\nGET / HTTP/1.1\r\nHost: a\r\n\r\n",
    "FOO / HTTP/1.1\r\nHost: a\r\n\r\n", "GE( / HTTP/1.1\r\n", "GET  / HTTP/1.1\r\n",
    "GET /%zz HTTP/1.1\r\nHost: a\r\n\r\n", "GET /aaaaaaaaaaaa HTTP/1.1\r\n", "GET /aaaaaaaaaaaaa HTTP/1.1\r\n",
    "GET /a\x01 HTTP/1.1\r\n", "GET /a HTTP/1.x\r\n", "GET /a HTTP/9.9\r\nHost: a\r\n\r\n", "GET /a HTTP/1.1x\r\n",
    "GET /a HTTP/1.1\rX", "GET /a\r\n", "GET http://a/b HTTP/1.1\r\nHost: a\r\n\r\n",
    -- Field lines: names, the colon, whitespace, values, their limits, the end of the head.
    head "X-Name: value", head "X-Name:value", head "X:   v", head "X:    v", head "X: ",
    head "Xxxxxxxx: v", head "Xxxxxxxxx: v", head "X(: v", head "X : v", head "X\r: v",
    head "X: 123456789012", head "X: 1234567890123", head "X: 123456789012   ", head "X: 123456789012 x",
    head "X: a\x01b", head "X: a\x7f", head "X: a\rb", head "X: \xff\xfe", head " X: v",
    "GET / HTTP/1.1\r\nHost: a\r\n\rX", "GET / HTTP/1.1\r\nHost: a\r\n\n",
    -- Chunk-size lines: zeros, digits and their limit, extensions, quoted values, escapes, BWS.
    chunked "5", chunked "0005", chunked "5g", chunked "1234567890abcdef", chunked "11234567890abcdef",
    chunked "5;a", chunked "5;abcd", chunked "5;abcde", chunked "5;a=b", chunked "5;a=bcdef",
    chunked "5;a=bcdefg", chunked "5 ; a = b", chunked "5;a=\"q q\"", chunked "5;a=\"q\\\"q\"",
    chunked "5;a=\"qqqqqq\"", chunked "5;a=\"q", chunked "5;a;b", chunked "5;a;b;c", chunked "5;",
    chunked "5; ", chunked "5;a b", chunked "5;a=\"\x01\"", chunked "5    ;a"
  ].map fun input => sameAsWhole "server" server input

#eval runCases <| [
    -- Status lines: the version, the code, the reason phrase and its limit, a missing reason.
    ("HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n", Method.get), ("HTTP/1.1 200\r\nContent-Length: 0\r\n\r\n", .get),
    ("HTTP/1.1 200 ABCDEF\r\nContent-Length: 0\r\n\r\n", .get), ("HTTP/1.1 200 ABCDEFG\r\n", .get),
    ("HTTP/1.1 2x0 OK\r\n", .get), ("HTTP/1.x 200 OK\r\n", .get), ("HTTP/1.1  200 OK\r\n", .get),
    ("HTTP/1.1 200 O\x01\r\n", .get), ("HTTP/1.1 200 OK\rX", .get), ("HTTP/1.0 200 OK\r\n\r\nbody", .get),
    -- Fields, obs-fold lines, and a chunked body with extensions.
    ("HTTP/1.1 200 OK\r\nX: a\r\n  b\r\nContent-Length: 0\r\n\r\n", .get),
    ("HTTP/1.1 200 OK\r\nX: a\r\n    b\r\nContent-Length: 0\r\n\r\n", .get),
    ("HTTP/1.1 200 OK\r\nX: 123456\r\n 123456\r\nContent-Length: 0\r\n\r\n", .get),
    ("HTTP/1.1 200 OK\r\nXxxxxxxxx: v\r\nContent-Length: 0\r\n\r\n", .get),
    ("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5;a=\"b\"\r\nhello\r\n0\r\nT: v\r\n\r\n", .get),
    ("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5;abcde\r\nhello\r\n0\r\n\r\n", .get),
    ("HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\n", .head)
  ].map fun (input, method) => sameAsWhole "client" (client method) input
