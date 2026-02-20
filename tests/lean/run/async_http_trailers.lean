import Std.Internal.Http
import Std.Internal.Async

open Std.Internal.IO Async
open Std Http
open Std.Http.Internal

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
    (config : Config := { lingeringTimeout := 3000, generateDate := false }) : IO ByteArray := Async.block do
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
  client.close
  Std.Http.Server.serveConnection server handler config
    |>.run
  let res ← client.recv?
  pure <| res.getD .empty


def assertStatus (name : String) (response : ByteArray) (status : String) : IO Unit := do
  let text := String.fromUTF8! response
  unless text.startsWith status do
    throw <| IO.userError s!"Test '{name}' failed:\nExpected {status}\nGot:\n{text.quote}"


def assertContains (name : String) (response : ByteArray) (needle : String) : IO Unit := do
  let text := String.fromUTF8! response
  unless text.contains needle do
    throw <| IO.userError s!"Test '{name}' failed:\nMissing {needle.quote}\nGot:\n{text.quote}"


def assertExact (name : String) (response : ByteArray) (expected : String) : IO Unit := do
  let text := String.fromUTF8! response
  if text != expected then
    throw <| IO.userError s!"Test '{name}' failed:\nExpected:\n{expected.quote}\nGot:\n{text.quote}"


def bodyHandler : TestHandler :=
  fun req => do
    let body : String ← req.body.readAll
    Response.ok |>.text body


def bad400 : String :=
  "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"


-- Chunked body without trailers.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw bodyHandler
  assertStatus "Chunked no trailers" response "HTTP/1.1 200"
  assertContains "Chunked no trailers body" response "hello"

-- Single trailer header.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\nChecksum: abc123\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw bodyHandler
  assertStatus "Single trailer" response "HTTP/1.1 200"
  assertContains "Single trailer body" response "hello"

-- Multiple trailer headers.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\nChecksum: abc123\x0d\nExpires: Thu, 01 Dec 1994 16:00:00 GMT\x0d\nX-Custom: value\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw bodyHandler
  assertStatus "Multiple trailers" response "HTTP/1.1 200"
  assertContains "Multiple trailers body" response "hello"

-- Terminal chunk extensions can precede trailers.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0;ext=val\x0d\nX-Trailer: yes\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw bodyHandler
  assertStatus "Terminal chunk extensions + trailers" response "HTTP/1.1 200"
  assertContains "Terminal chunk extensions + trailers body" response "hello"

-- Trailer name and value limits.
#eval show IO _ from do
  let exactName := String.ofList (List.replicate 256 'X')
  let longName := String.ofList (List.replicate 257 'X')
  let exactValue := String.ofList (List.replicate 8192 'v')
  let longValue := String.ofList (List.replicate 8193 'v')

  let (clientA, serverA) ← Mock.new
  let rawA := s!"POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nabc\x0d\n0\x0d\n{exactName}: value\x0d\n\x0d\n".toUTF8
  let responseA ← sendRaw clientA serverA rawA bodyHandler
  assertStatus "Trailer name at 256" responseA "HTTP/1.1 200"

  let (clientB, serverB) ← Mock.new
  let rawB := s!"POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nabc\x0d\n0\x0d\n{longName}: value\x0d\n\x0d\n".toUTF8
  let responseB ← sendRaw clientB serverB rawB bodyHandler
  assertExact "Trailer name exceeds 256" responseB bad400

  let (clientC, serverC) ← Mock.new
  let rawC := s!"POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nabc\x0d\n0\x0d\nX-Exact: {exactValue}\x0d\n\x0d\n".toUTF8
  let responseC ← sendRaw clientC serverC rawC bodyHandler
  assertStatus "Trailer value at 8192" responseC "HTTP/1.1 200"

  let (clientD, serverD) ← Mock.new
  let rawD := s!"POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nabc\x0d\n0\x0d\nX-Too-Long: {longValue}\x0d\n\x0d\n".toUTF8
  let responseD ← sendRaw clientD serverD rawD bodyHandler
  assertExact "Trailer value exceeds 8192" responseD bad400

-- maxTrailerHeaders enforcement.
#eval show IO _ from do
  let config2 : Config := { lingeringTimeout := 3000, maxTrailerHeaders := 2, generateDate := false }

  let (clientA, serverA) ← Mock.new
  let okRaw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nabc\x0d\n0\x0d\nT1: a\x0d\nT2: b\x0d\n\x0d\n".toUTF8
  let okResponse ← sendRaw clientA serverA okRaw bodyHandler (config := config2)
  assertStatus "maxTrailerHeaders exact limit" okResponse "HTTP/1.1 200"

  let (clientB, serverB) ← Mock.new
  let badRaw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nabc\x0d\n0\x0d\nT1: a\x0d\nT2: b\x0d\nT3: c\x0d\n\x0d\n".toUTF8
  let badResponse ← sendRaw clientB serverB badRaw bodyHandler (config := config2)
  assertExact "maxTrailerHeaders overflow" badResponse bad400

  let config0 : Config := { lingeringTimeout := 3000, maxTrailerHeaders := 0, generateDate := false }

  let (clientC, serverC) ← Mock.new
  let rejectAny := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nabc\x0d\n0\x0d\nX-Trailer: rejected\x0d\n\x0d\n".toUTF8
  let responseC ← sendRaw clientC serverC rejectAny bodyHandler (config := config0)
  assertExact "maxTrailerHeaders=0 rejects trailers" responseC bad400

  let (clientD, serverD) ← Mock.new
  let noTrailer := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nabc\x0d\n0\x0d\n\x0d\n".toUTF8
  let responseD ← sendRaw clientD serverD noTrailer bodyHandler (config := config0)
  assertStatus "maxTrailerHeaders=0 no trailers" responseD "HTTP/1.1 200"

-- Trailer syntax validation.
#eval show IO _ from do
  let (clientA, serverA) ← Mock.new
  let noColon := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nabc\x0d\n0\x0d\nBadTrailer value\x0d\n\x0d\n".toUTF8
  let responseA ← sendRaw clientA serverA noColon bodyHandler
  assertExact "Trailer without colon" responseA bad400

  let (clientB, serverB) ← Mock.new
  let leadingWS := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nabc\x0d\n0\x0d\n X-Bad: folded\x0d\n\x0d\n".toUTF8
  let responseB ← sendRaw clientB serverB leadingWS bodyHandler
  assertExact "Trailer leading whitespace" responseB bad400

  let (clientC, serverC) ← Mock.new
  let spaceName := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nabc\x0d\n0\x0d\nBad Name: value\x0d\n\x0d\n".toUTF8
  let responseC ← sendRaw clientC serverC spaceName bodyHandler
  assertExact "Trailer name contains space" responseC bad400

-- Trailer byte-level validation.
#eval show IO _ from do
  let (clientA, serverA) ← Mock.new
  let beforeName := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nabc\x0d\n0\x0d\nX-Bad".toUTF8
  let afterName := "Name: value\x0d\n\x0d\n".toUTF8
  let responseA ← sendRaw clientA serverA (beforeName ++ ByteArray.mk #[0] ++ afterName) bodyHandler
  assertExact "NUL in trailer name" responseA bad400

  let (clientB, serverB) ← Mock.new
  let beforeValue := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nabc\x0d\n0\x0d\nX-Header: bad".toUTF8
  let afterValue := "value\x0d\n\x0d\n".toUTF8
  let responseB ← sendRaw clientB serverB (beforeValue ++ ByteArray.mk #[0] ++ afterValue) bodyHandler
  assertExact "NUL in trailer value" responseB bad400

  let (clientC, serverC) ← Mock.new
  let responseC ← sendRaw clientC serverC (beforeValue ++ ByteArray.mk #[0x01] ++ afterValue) bodyHandler
  assertExact "Control char in trailer value" responseC bad400

-- Incomplete trailer section with client close yields no response bytes.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n3\x0d\nabc\x0d\n0\x0d\nX-Trailer: value\x0d\n".toUTF8
  let response ← sendRawAndClose client server raw bodyHandler
  assert! response.size == 0

-- Trailer encoding emits terminal chunk plus trailer headers.
#eval show IO _ from Async.block do
  let trailer := Trailer.empty
    |>.insert (.mk "checksum") (.mk "abc123")
    |>.insert (.mk "expires") (.mk "Thu, 01 Dec 1994")
  let encoded := (Encode.encode (v := .v11) ChunkedBuffer.empty trailer).toByteArray
  let text := String.fromUTF8! encoded
  assert! text.contains "0\x0d\n"
  assert! text.contains "Checksum: abc123\x0d\n"
  assert! text.contains "Expires: Thu, 01 Dec 1994\x0d\n"

-- Empty trailer encoding is exactly terminal chunk CRLF CRLF.
#eval show IO _ from Async.block do
  let encoded := (Encode.encode (v := .v11) ChunkedBuffer.empty Trailer.empty).toByteArray
  let text := String.fromUTF8! encoded
  assert! text == "0\x0d\n\x0d\n"
