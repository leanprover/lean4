import Std.Internal.Http
import Std.Internal.Async

open Std.Internal.IO Async
open Std Http

abbrev TestHandler := Request Body.Incoming → ContextAsync (Response Body.AnyBody)

instance : Std.Http.Server.Handler TestHandler where
  onRequest handler request := handler request

def sendRaw
    (client : Mock.Client)
    (server : Mock.Server)
    (raw : ByteArray)
    (handler : TestHandler)
    (config : Config) : IO ByteArray := Async.block do
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

def baseConfig : Config := {
  lingeringTimeout := 3000
  generateDate := false
  maxChunkExtNameLength := 4
  maxChunkExtValueLength := 4
}

-- Baseline chunked request without extensions.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler baseConfig
  assertStatusPrefix "Chunked baseline with strict ext limits" response "HTTP/1.1 200"

-- Chunk extension name exactly at limit should be accepted.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5;name=1\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler baseConfig
  assertStatusPrefix "Chunk extension name at limit" response "HTTP/1.1 200"

-- Chunk extension name exceeding limit should be rejected.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5;toolong=1\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler baseConfig
  assertStatusPrefix "Chunk extension name too long" response "HTTP/1.1 400"

-- Chunk extension value exactly at limit should be accepted.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5;name=abcd\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler baseConfig
  assertStatusPrefix "Chunk extension value at limit" response "HTTP/1.1 200"

-- Chunk extension value exceeding limit should be rejected.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5;name=abcde\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler baseConfig
  assertStatusPrefix "Chunk extension value too long" response "HTTP/1.1 400"

-- Hypothesis: quoted extension values should also honor maxChunkExtValueLength.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5;name=\"abcde\"\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler baseConfig
  assertStatusPrefix "Quoted chunk extension value too long" response "HTTP/1.1 400"

-- Invalid extension-name token character should be rejected.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5;na@e=1\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler baseConfig
  assertStatusPrefix "Invalid chunk extension token char" response "HTTP/1.1 400"

-- One invalid extension among many should still reject the request.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5;a=1;b=2;toolong=3\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler baseConfig
  assertStatusPrefix "Mixed valid and invalid chunk extensions" response "HTTP/1.1 400"
