import Std.Internal.Http
import Std.Internal.Async

open Std.Internal.IO Async
open Std Http

abbrev TestHandler := Request Body.Incoming → ContextAsync (Response Body.AnyBody)

instance : Std.Http.Server.Handler TestHandler where
  onRequest handler request := handler request

/-- Send raw bytes to the server and return the full response payload. -/
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
  pure (res.getD .empty)

def assertStatusPrefix (name : String) (response : ByteArray) (prefix_ : String) : IO Unit := do
  let responseStr := String.fromUTF8! response
  unless responseStr.startsWith prefix_ do
    throw <| IO.userError s!"Test '{name}' failed:\nExpected status prefix {prefix_.quote}\nGot:\n{responseStr.quote}"

def echoBodyHandler : TestHandler := fun req => do
  let body : String ← req.body.readAll
  Response.ok |>.text body

-- Positive control: normal chunked request is accepted.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertStatusPrefix "Chunked baseline accepted" response "HTTP/1.1 200"

-- Duplicate TE lines where combined value is "chunked, gzip" must be rejected.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nTransfer-Encoding: gzip\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertStatusPrefix "Duplicate TE with chunked then gzip" response "HTTP/1.1 400"

-- Unsupported transfer coding before chunked must be rejected.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: gzip, chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertStatusPrefix "Unsupported gzip, chunked transfer coding" response "HTTP/1.1 400"

-- Non-chunked transfer coding is unsupported.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: identity\x0d\nConnection: close\x0d\n\x0d\nhello".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertStatusPrefix "Unsupported identity transfer coding" response "HTTP/1.1 400"

-- TE + CL mixed framing must be rejected.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertStatusPrefix "TE + CL mixed framing" response "HTTP/1.1 400"

-- Duplicate chunked codings are invalid.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked, chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertStatusPrefix "Duplicate chunked coding in one header" response "HTTP/1.1 400"

-- Malformed TE with empty coding token is invalid.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: ,chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertStatusPrefix "Malformed transfer-encoding token list" response "HTTP/1.1 400"
