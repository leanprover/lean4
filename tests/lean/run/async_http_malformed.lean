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
  pure <| res.getD .empty


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
  pure <| res.getD .empty


def assertStatus (name : String) (response : ByteArray) (status : String) : IO Unit := do
  let responseStr := String.fromUTF8! response
  unless responseStr.startsWith status do
    throw <| IO.userError s!"Test '{name}' failed:\nExpected status: {status}\nGot:\n{responseStr.quote}"


def assertExact (name : String) (response : ByteArray) (expected : String) : IO Unit := do
  let responseStr := String.fromUTF8! response
  if responseStr != expected then
    throw <| IO.userError s!"Test '{name}' failed:\nExpected:\n{expected.quote}\nGot:\n{responseStr.quote}"


def assertContains (name : String) (response : ByteArray) (needle : String) : IO Unit := do
  let responseStr := String.fromUTF8! response
  unless responseStr.contains needle do
    throw <| IO.userError s!"Test '{name}' failed:\nExpected to contain: {needle.quote}\nGot:\n{responseStr.quote}"


def headerSection (response : ByteArray) : String :=
  (String.fromUTF8! response).splitOn "\x0d\n\x0d\n" |>.headD ""


def okHandler : TestHandler :=
  fun _ => Response.ok |>.text "ok"


def bad400 : String :=
  "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"


def bad505 : String :=
  "HTTP/1.1 505 HTTP Version Not Supported\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"


def ok200 : String :=
  "HTTP/1.1 200 OK\x0d\nContent-Length: 2\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\nContent-Type: text/plain; charset=utf-8\x0d\n\x0d\nok"


def ok200Head : String :=
  "HTTP/1.1 200 OK\x0d\nContent-Length: 2\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\nContent-Type: text/plain; charset=utf-8\x0d\n\x0d\n"


def notImplemented : String :=
  "HTTP/1.1 501 Not Implemented\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"


-- Client-mode response parsing regressions.
#eval show IO _ from do
  let machineA : Protocol.H1.Machine .sending := { config := {} }
  let rawA := "HTTP/1.1 200 OK\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\n\x0d\n"
  let (machineA, stepA) := (machineA.feed rawA.toUTF8).step
  let failedA := stepA.events.any fun
    | .failed _ => true
    | _ => false
  if failedA then
    throw <| IO.userError s!"Test 'Client mode parses response status-line with headers' failed:\nUnexpected failure events: {repr stepA.events}"

  let endedA := stepA.events.any fun
    | .endHeaders _ => true
    | _ => false
  unless endedA do
    throw <| IO.userError s!"Test 'Client mode parses response status-line with headers' failed:\nMissing endHeaders event: {repr stepA.events}"

  unless machineA.reader.messageHead.status == .ok do
    throw <| IO.userError s!"Test 'Client mode parses response status-line with headers' failed:\nUnexpected status: {repr machineA.reader.messageHead.status}"

  unless machineA.reader.messageHead.headers.hasEntry Header.Name.contentLength (Header.Value.ofString! "0") do
    throw <| IO.userError s!"Test 'Client mode parses response status-line with headers' failed:\nMissing Content-Length header in parsed response"

  let machineB : Protocol.H1.Machine .sending := { config := {} }
  let rawB := "HTTP/1.1 204 No Content\x0d\n\x0d\n"
  let (_machineB, stepB) := (machineB.feed rawB.toUTF8).step
  let failedB := stepB.events.any fun
    | .failed _ => true
    | _ => false
  if failedB then
    throw <| IO.userError s!"Test 'Client mode parses headerless response status-line' failed:\nUnexpected failure events: {repr stepB.events}"

  let needMoreB := stepB.events.any fun
    | .needMoreData _ => true
    | _ => false
  if needMoreB then
    throw <| IO.userError s!"Test 'Client mode parses headerless response status-line' failed:\nUnexpected needMoreData event: {repr stepB.events}"

  let endedB := stepB.events.any fun
    | .endHeaders _ => true
    | _ => false
  unless endedB do
    throw <| IO.userError s!"Test 'Client mode parses headerless response status-line' failed:\nMissing endHeaders event: {repr stepB.events}"

-- Host header rules.
#eval show IO _ from do
  let (clientA, serverA) ← Mock.new
  let missingHost := "GET / HTTP/1.1\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let responseA ← sendRaw clientA serverA missingHost okHandler
  assertExact "Missing Host header" responseA bad400

  let (clientB, serverB) ← Mock.new
  let emptyHost := "GET / HTTP/1.1\x0d\nHost: \x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let responseB ← sendRaw clientB serverB emptyHost okHandler
  assertExact "Empty Host header" responseB bad400

  let (clientC, serverC) ← Mock.new
  let multiHost := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nHost: other.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let responseC ← sendRaw clientC serverC multiHost okHandler
  assertExact "Multiple Host headers" responseC bad400

-- HTTP version handling.
#eval show IO _ from do
  let (clientA, serverA) ← Mock.new
  let rawA := "GET / HTTP/2.0\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let responseA ← sendRaw clientA serverA rawA okHandler
  assertExact "HTTP/2.0 rejected" responseA bad505

  let (clientB, serverB) ← Mock.new
  let rawB := "GET / HTTP/1.0\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let responseB ← sendRaw clientB serverB rawB okHandler
  assertExact "HTTP/1.0 rejected" responseB bad505

-- Request-line parsing failures.
#eval show IO _ from do
  let (clientA, serverA) ← Mock.new
  let missingVersion := "GET /\x0d\nHost: example.com\x0d\n\x0d\n".toUTF8
  let responseA ← sendRaw clientA serverA missingVersion okHandler
  assertExact "Missing version in request-line" responseA bad400

  let (clientB, serverB) ← Mock.new
  let missingUri := "GET  HTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n".toUTF8
  let responseB ← sendRaw clientB serverB missingUri okHandler
  assertExact "Missing URI in request-line" responseB bad400

  let (clientC, serverC) ← Mock.new
  let extraSpaces := "GET  /  HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let responseC ← sendRaw clientC serverC extraSpaces okHandler
  assertExact "Extra spaces in request-line" responseC bad400

  let (clientD, serverD) ← Mock.new
  let emptyLine := "\x0d\n\x0d\n".toUTF8
  let responseD ← sendRaw clientD serverD emptyLine okHandler
  assertExact "Empty request-line" responseD bad400

  let (clientE, serverE) ← Mock.new
  let whitespaceOnly := "   \x0d\n\x0d\n".toUTF8
  let responseE ← sendRaw clientE serverE whitespaceOnly okHandler
  assertExact "Whitespace-only request-line" responseE bad400

  let (clientF, serverF) ← Mock.new
  let noSpaces := "GETHTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n".toUTF8
  let responseF ← sendRaw clientF serverF noSpaces okHandler
  assertExact "No spaces in request-line" responseF bad400

  let (clientG, serverG) ← Mock.new
  let leadingCRLF := "\x0d\nGET / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let responseG ← sendRaw clientG serverG leadingCRLF okHandler
  assertExact "Leading CRLF before request-line" responseG bad400

  let (clientH, serverH) ← Mock.new
  let garbageAfterVersion := "GET / HTTP/1.1 xxxxxx\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let responseH ← sendRaw clientH serverH garbageAfterVersion okHandler
  assertExact "Garbage after request-line version" responseH bad400

-- Method rules.
#eval show IO _ from do
  let (clientA, serverA) ← Mock.new
  let invalidMethod := "FOOBAR / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let responseA ← sendRaw clientA serverA invalidMethod okHandler
  assertExact "Unknown method returns 501" responseA notImplemented

  let (clientB, serverB) ← Mock.new
  let lowercaseMethod := "get / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let responseB ← sendRaw clientB serverB lowercaseMethod okHandler
  assertExact "Lowercase method rejected" responseB bad400

  let (clientC, serverC) ← Mock.new
  let nonAsciiMethod := "GÉT / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let responseC ← sendRaw clientC serverC nonAsciiMethod okHandler
  assertExact "Non-ASCII method rejected" responseC bad400

  let (clientD, serverD) ← Mock.new
  let longMethod := String.ofList (List.replicate 20 'G')
  let rawD := s!"{longMethod} / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let responseD ← sendRaw clientD serverD rawD okHandler
  assertExact "Method too long" responseD bad400

-- HEAD framing and authority-form rules.
#eval show IO _ from do
  let (clientA, serverA) ← Mock.new
  let headReq := "HEAD / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let responseA ← sendRaw clientA serverA headReq okHandler
  assertExact "HEAD omits body bytes" responseA ok200Head

  let (clientB, serverB) ← Mock.new
  let badAuthority := "GET example.com:443 HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let responseB ← sendRaw clientB serverB badAuthority okHandler
  assertExact "GET authority-form rejected" responseB bad400

  let (clientC, serverC) ← Mock.new
  let okAuthority := "CONNECT example.com:443 HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let responseC ← sendRaw clientC serverC okAuthority okHandler
  assertExact "CONNECT authority-form accepted" responseC ok200

-- h11-inspired: GET and HEAD should use the same framing headers.
#eval show IO _ from do
  let handler : TestHandler := fun _ => Response.ok |>.text "hello"

  let (clientA, serverA) ← Mock.new
  let getReq := "GET /frame HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let getResponse ← sendRaw clientA serverA getReq handler

  let (clientB, serverB) ← Mock.new
  let headReq := "HEAD /frame HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let headResponse ← sendRaw clientB serverB headReq handler

  let getHeaders := headerSection getResponse
  let headHeaders := headerSection headResponse
  if getHeaders != headHeaders then
    throw <| IO.userError s!"Test 'HEAD framing headers parity' failed:\nGET headers:\n{getHeaders.quote}\nHEAD headers:\n{headHeaders.quote}"

  assertContains "GET framing body present" getResponse "hello"
  let headText := String.fromUTF8! headResponse
  if headText.contains "hello" then
    throw <| IO.userError s!"Test 'HEAD framing body omitted' failed:\n{headText.quote}"

-- Header syntax and byte-level validation.
#eval show IO _ from do
  let (clientA, serverA) ← Mock.new
  let noColon := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nBadHeader value\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let responseA ← sendRaw clientA serverA noColon okHandler
  assertExact "Header without colon" responseA bad400

  let (clientB, serverB) ← Mock.new
  let obsFold := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\n X-Bad: folded\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let responseB ← sendRaw clientB serverB obsFold okHandler
  assertExact "Leading whitespace header" responseB bad400

  let (clientC, serverC) ← Mock.new
  let beforeName := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nX-Bad".toUTF8
  let afterName := "Header: value\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let responseC ← sendRaw clientC serverC (beforeName ++ ByteArray.mk #[0] ++ afterName) okHandler
  assertExact "NUL in header name" responseC bad400

  let (clientD, serverD) ← Mock.new
  let beforeValue := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nX-Header: bad".toUTF8
  let afterValue := "value\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let responseD ← sendRaw clientD serverD (beforeValue ++ ByteArray.mk #[0] ++ afterValue) okHandler
  assertExact "NUL in header value" responseD bad400

  let (clientE, serverE) ← Mock.new
  let beforeCtrl := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nX-Header: bad".toUTF8
  let afterCtrl := "value\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let responseE ← sendRaw clientE serverE (beforeCtrl ++ ByteArray.mk #[0x01] ++ afterCtrl) okHandler
  assertExact "Control char in header value" responseE bad400

  let (clientF, serverF) ← Mock.new
  let spaceInName := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nBad Header: value\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let responseF ← sendRaw clientF serverF spaceInName okHandler
  assertExact "Space in header name" responseF bad400

-- Lenient-but-supported parsing behavior.
#eval show IO _ from do
  let (clientA, serverA) ← Mock.new
  let bareLF := "GET / HTTP/1.1\nHost: example.com\nConnection: close\n\n".toUTF8
  let responseA ← sendRaw clientA serverA bareLF okHandler
  assertExact "Bare LF line endings accepted" responseA bad400

  let (clientB, serverB) ← Mock.new
  let splitHeaders := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nX-Inject: value\x0d\nEvil: injected\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let responseB ← sendRaw clientB serverB splitHeaders okHandler
  assertExact "CRLF split into two headers" responseB ok200

  let (clientC, serverC) ← Mock.new
  let tabValue := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nX-Tab: value\twith\ttabs\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let responseC ← sendRaw clientC serverC tabValue okHandler
  assertExact "Tab in header value accepted" responseC ok200

  let (clientD, serverD) ← Mock.new
  let absoluteUri := "GET http://example.com/path HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let responseD ← sendRaw clientD serverD absoluteUri okHandler
  assertExact "Absolute-form URI accepted" responseD ok200

  let (clientE, serverE) ← Mock.new
  let colonValue := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nBad:Name: value\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let responseE ← sendRaw clientE serverE colonValue okHandler
  assertExact "Additional colon remains in value" responseE ok200

-- Content-Length validation.
#eval show IO _ from do
  let (clientA, serverA) ← Mock.new
  let nonNumeric := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: abc\x0d\nConnection: close\x0d\n\x0d\nbody".toUTF8
  let responseA ← sendRaw clientA serverA nonNumeric okHandler
  assertExact "Non-numeric Content-Length" responseA bad400

  let (clientB, serverB) ← Mock.new
  let negative := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: -1\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let responseB ← sendRaw clientB serverB negative okHandler
  assertExact "Negative Content-Length" responseB bad400

  let (clientC, serverC) ← Mock.new
  let duplicateCl := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length: 5\x0d\nContent-Length: 10\x0d\nConnection: close\x0d\n\x0d\nhello".toUTF8
  let responseC ← sendRaw clientC serverC duplicateCl okHandler
  assertExact "Duplicate Content-Length mismatch" responseC bad400

-- Transfer-Encoding normalization.
#eval show IO _ from do
  let (clientA, serverA) ← Mock.new
  let mixedCase := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: Chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let responseA ← sendRaw clientA serverA mixedCase (fun req => do
    let body : String ← req.body.readAll
    Response.ok |>.text body)
  assertStatus "Mixed-case chunked accepted" responseA "HTTP/1.1 200"
  assertContains "Mixed-case chunked body" responseA "hello"

  let (clientB, serverB) ← Mock.new
  let teOWS := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked \x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let responseB ← sendRaw clientB serverB teOWS (fun req => do
    let body : String ← req.body.readAll
    Response.ok |>.text body)
  assertStatus "Transfer-Encoding trailing OWS accepted" responseB "HTTP/1.1 200"
  assertContains "Transfer-Encoding trailing OWS body" responseB "hello"

  let (clientC, serverC) ← Mock.new
  let doubleChunked := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked, chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let responseC ← sendRaw clientC serverC doubleChunked okHandler
  assertExact "Double chunked rejected" responseC bad400

-- Size limits.
#eval show IO _ from do
  let (clientA, serverA) ← Mock.new
  let longName := String.ofList (List.replicate 257 'X')
  let rawA := s!"GET / HTTP/1.1\x0d\nHost: example.com\x0d\n{longName}: value\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let responseA ← sendRaw clientA serverA rawA okHandler
  assertExact "Header name too long" responseA bad400

  let (clientB, serverB) ← Mock.new
  let longUri := "/" ++ String.ofList (List.replicate 9000 'a')
  let rawB := s!"GET {longUri} HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
  let responseB ← sendRaw clientB serverB rawB okHandler
  assertExact "URI too long" responseB bad400

-- Empty connection closes silently (no response bytes).
#eval show IO _ from do
  let (client, server) ← Mock.new
  let response ← sendRawAndClose client server ByteArray.empty okHandler
  assert! response.size == 0

-- h11-inspired: early invalid-byte detection before CRLF.
#eval show IO _ from do
  let (clientA, serverA) ← Mock.new
  let responseA ← sendRawAndClose clientA serverA (ByteArray.mk #[0x00]) okHandler
  assertExact "Early invalid NUL" responseA bad400

  let (clientB, serverB) ← Mock.new
  let responseB ← sendRawAndClose clientB serverB (ByteArray.mk #[0x20]) okHandler
  assertExact "Early invalid SP" responseB bad400

  let (clientC, serverC) ← Mock.new
  let responseC ← sendRawAndClose clientC serverC (ByteArray.mk #[0x16, 0x03, 0x01, 0x00, 0xa5]) okHandler
  assertExact "Early invalid TLS prefix" responseC bad400
