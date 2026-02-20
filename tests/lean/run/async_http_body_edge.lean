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
    (config : Config := { lingeringTimeout := 1000, generateDate := false }) : IO ByteArray := Async.block do
  client.send raw
  Std.Http.Server.serveConnection server handler config
    |>.run
  let res ← client.recv?
  pure (res.getD .empty)


def sendRawAndClose
    (client : Mock.Client)
    (server : Mock.Server)
    (raw : ByteArray)
    (handler : TestHandler)
    (config : Config := { lingeringTimeout := 1000, generateDate := false }) : IO ByteArray := Async.block do
  client.send raw
  client.getSendChan.close
  Std.Http.Server.serveConnection server handler config
    |>.run
  let res ← client.recv?
  pure (res.getD .empty)


def responseText (response : ByteArray) : String :=
  String.fromUTF8! response


def assertStatusPrefix (name : String) (response : ByteArray) (prefix_ : String) : IO Unit := do
  let text := responseText response
  unless text.startsWith prefix_ do
    throw <| IO.userError s!"Test '{name}' failed:\nExpected status prefix {prefix_.quote}\nGot:\n{text.quote}"


def assertContains (name : String) (response : ByteArray) (needle : String) : IO Unit := do
  let text := responseText response
  unless text.contains needle do
    throw <| IO.userError s!"Test '{name}' failed:\nMissing {needle.quote}\nGot:\n{text.quote}"


def assertNotContains (name : String) (response : ByteArray) (needle : String) : IO Unit := do
  let text := responseText response
  if text.contains needle then
    throw <| IO.userError s!"Test '{name}' failed:\nUnexpected {needle.quote}\nGot:\n{text.quote}"


def assertExact (name : String) (response : ByteArray) (expected : String) : IO Unit := do
  let text := responseText response
  if text != expected then
    throw <| IO.userError s!"Test '{name}' failed:\nExpected:\n{expected.quote}\nGot:\n{text.quote}"


def countOccurrences (s : String) (needle : String) : Nat :=
  if needle.isEmpty then
    0
  else
    (s.splitOn needle).length - 1


def assertStatusCount (name : String) (response : ByteArray) (expected : Nat) : IO Unit := do
  let text := responseText response
  let got := countOccurrences text "HTTP/1.1 "
  if got != expected then
    throw <| IO.userError s!"Test '{name}' failed:\nExpected {expected} responses but saw {got}\n{text.quote}"


def bad400 : String :=
  "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"


def echoBodyHandler : TestHandler := fun req => do
  let body : String ← req.body.readAll
  Response.ok |>.text body


-- Content-Length body is read exactly.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST /echo HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\n\x0d\nhello".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertStatusPrefix "CL body accepted" response "HTTP/1.1 200"
  assertContains "CL body echoed" response "hello"

-- Chunked body baseline.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST /chunked HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertStatusPrefix "Chunked baseline" response "HTTP/1.1 200"
  assertContains "Chunked baseline body" response "hello"

-- Uppercase and leading-zero chunk-size are accepted.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST /chunked HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n000A\x0d\n0123456789\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertStatusPrefix "Chunk-size uppercase+leading-zero" response "HTTP/1.1 200"
  assertContains "Chunk-size uppercase+leading-zero body" response "0123456789"

-- Chunk extensions with token and quoted value are accepted.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST /chunked HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5;ext=value;quoted=\"ok\"\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertStatusPrefix "Chunk extensions accepted" response "HTTP/1.1 200"
  assertContains "Chunk extensions body" response "hello"

-- h11-inspired: invalid chunk-size token is rejected.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST /bad HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\nG\x0d\nabc\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertExact "Invalid chunk-size token" response bad400

-- h11-inspired: reject bad bytes where chunk terminator must be CRLF.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST /smuggle HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nxxx__1a\x0d\n".toUTF8
  let response ← sendRawAndClose client server raw echoBodyHandler
  assertExact "Chunk terminator bytes validated" response bad400

-- Missing terminal 0-chunk is rejected once EOF arrives.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST /incomplete HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n".toUTF8
  let response ← sendRawAndClose client server raw echoBodyHandler
  assertExact "Missing terminal zero chunk" response bad400

-- TE+CL mixed framing is rejected.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST /mix HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertExact "TE+CL rejected" response bad400

-- Duplicate chunked coding is rejected.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST /dup HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked, chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertExact "Duplicate chunked coding" response bad400

-- Duplicate Transfer-Encoding lines with unsupported coding are rejected.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST /dup-lines HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nTransfer-Encoding: gzip\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertExact "Duplicate TE headers with gzip" response bad400

-- Unsupported transfer codings are rejected.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST /gzip HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: gzip, chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertExact "gzip, chunked rejected" response bad400

#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST /identity HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: identity\x0d\nConnection: close\x0d\n\x0d\nhello".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertExact "identity transfer-coding rejected" response bad400

-- Malformed Transfer-Encoding token list is rejected.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST /bad-te-list HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: ,chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertExact "Malformed Transfer-Encoding token list" response bad400

-- Strict chunk-extension name/value limits.
#eval show IO _ from do
  let config : Config := {
    lingeringTimeout := 1000
    generateDate := false
    maxChunkExtNameLength := 4
    maxChunkExtValueLength := 4
  }

  let (clientA, serverA) ← Mock.new
  let okName := "POST /ok-name HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5;name=1\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let responseA ← sendRaw clientA serverA okName echoBodyHandler (config := config)
  assertStatusPrefix "Chunk ext name at limit" responseA "HTTP/1.1 200"

  let (clientB, serverB) ← Mock.new
  let badName := "POST /bad-name HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5;toolong=1\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let responseB ← sendRaw clientB serverB badName echoBodyHandler (config := config)
  assertExact "Chunk ext name too long" responseB bad400

  let (clientC, serverC) ← Mock.new
  let okValue := "POST /ok-value HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5;name=abcd\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let responseC ← sendRaw clientC serverC okValue echoBodyHandler (config := config)
  assertStatusPrefix "Chunk ext value at limit" responseC "HTTP/1.1 200"

  let (clientD, serverD) ← Mock.new
  let badQuoted := "POST /bad-value HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5;name=\"abcde\"\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let responseD ← sendRaw clientD serverD badQuoted echoBodyHandler (config := config)
  assertExact "Quoted chunk ext value too long" responseD bad400

  let (clientE, serverE) ← Mock.new
  let badToken := "POST /bad-token HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5;na@e=1\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let responseE ← sendRaw clientE serverE badToken echoBodyHandler (config := config)
  assertExact "Invalid chunk ext token char" responseE bad400

  let (clientF, serverF) ← Mock.new
  let mixed := "POST /mixed-ext HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5;a=1;b=2;toolong=3\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let responseF ← sendRaw clientF serverF mixed echoBodyHandler (config := config)
  assertExact "Mixed valid/invalid chunk extensions" responseF bad400

-- maxChunkExtensions boundary is enforced.
#eval show IO _ from do
  let config : Config := {
    lingeringTimeout := 1000
    generateDate := false
    maxChunkExtensions := 2
  }

  let (clientA, serverA) ← Mock.new
  let okRaw := "POST /ext-count HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5;a=1;b=2\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let okResponse ← sendRaw clientA serverA okRaw echoBodyHandler (config := config)
  assertStatusPrefix "maxChunkExtensions at limit" okResponse "HTTP/1.1 200"

  let (clientB, serverB) ← Mock.new
  let badRaw := "POST /ext-count-overflow HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5;a=1;b=2;c=3\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let badResponse ← sendRaw clientB serverB badRaw echoBodyHandler (config := config)
  assertExact "maxChunkExtensions overflow" badResponse bad400

-- Content-Length with leading zeros is accepted.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST /leading-zeros HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 005\x0d\nConnection: close\x0d\n\x0d\nhello".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertStatusPrefix "Content-Length leading zeros" response "HTTP/1.1 200"
  assertContains "Content-Length leading zeros body" response "hello"

-- Very large Content-Length is rejected with 413.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST /too-large HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 99999999999999999999\x0d\nConnection: close\x0d\n\x0d\nhello".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertStatusPrefix "Huge Content-Length" response "HTTP/1.1 413"

-- Duplicate Content-Length (same and different values) are rejected.
#eval show IO _ from do
  let (clientA, serverA) ← Mock.new
  let same := "POST /dup-cl-same HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 5\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\n\x0d\nhello".toUTF8
  let responseA ← sendRaw clientA serverA same echoBodyHandler
  assertExact "Duplicate Content-Length same" responseA bad400

  let (clientB, serverB) ← Mock.new
  let diff := "POST /dup-cl-diff HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 3\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\n\x0d\nabc".toUTF8
  let responseB ← sendRaw clientB serverB diff echoBodyHandler
  assertExact "Duplicate Content-Length different" responseB bad400

-- Chunk-size line trailing whitespace is rejected.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST /bad-space HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5 \x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertExact "Chunk-size trailing space" response bad400

-- Transfer-Encoding trailing OWS is currently accepted.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST /te-ows HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked \x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertStatusPrefix "Transfer-Encoding trailing OWS" response "HTTP/1.1 200"
  assertContains "Transfer-Encoding trailing OWS body" response "hello"

-- h11-inspired: early invalid-byte detection before CRLF.
#eval show IO _ from do
  let (clientA, serverA) ← Mock.new
  let responseA ← sendRawAndClose clientA serverA (ByteArray.mk #[0x00]) echoBodyHandler
  assertExact "Early invalid NUL" responseA bad400

  let (clientB, serverB) ← Mock.new
  let responseB ← sendRawAndClose clientB serverB (ByteArray.mk #[0x20]) echoBodyHandler
  assertExact "Early invalid SP" responseB bad400

  let (clientC, serverC) ← Mock.new
  let responseC ← sendRawAndClose clientC serverC (ByteArray.mk #[0x16, 0x03, 0x01, 0x00, 0xa5]) echoBodyHandler
  assertExact "Early invalid TLS prefix" responseC bad400

-- h11-inspired: reject garbage after request-line version token.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "GET / HTTP/1.1 xxxxxx\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertExact "Garbage after request-line" response bad400

-- Extra bytes beyond Content-Length become the next pipelined request.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw :=
    ("POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 5\x0d\n\x0d\nhello" ++
     "GET /second HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n").toUTF8

  let response ← sendRaw client server raw (fun req => do
    let mut body := ByteArray.empty
    for chunk in req.body do
      body := body ++ chunk.data
    Response.ok |>.text s!"{toString req.head.uri}:{String.fromUTF8! body}")

  assertStatusCount "Pipelined parse after exact CL" response 2
  assertContains "Pipelined first response" response "/:hello"
  assertContains "Pipelined second response" response "/second:"
  assertNotContains "No parse confusion" response "/second:hello"
