import Std.Internal.Http
import Std.Internal.Async

open Std.Internal.IO Async
open Std Http

abbrev TestHandler := Request Body.Incoming → ContextAsync (Response Body.Outgoing)

instance : Std.Http.Server.Handler TestHandler where
  onRequest handler request := handler request

def sendRaw
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

def assertContains (name : String) (response : ByteArray) (needle : String) : IO Unit := do
  let responseStr := String.fromUTF8! response
  unless responseStr.contains needle do
    throw <| IO.userError s!"Test '{name}' failed:\nExpected to contain: {needle.quote}\nGot:\n{responseStr.quote}"

def assertStatusOneOf (name : String) (response : ByteArray) (prefixes : Array String) : IO Unit := do
  let responseStr := String.fromUTF8! response
  let ok := prefixes.any (fun prefix_ => responseStr.startsWith prefix_)
  unless ok do
    throw <| IO.userError s!"Test '{name}' failed:\nExpected one of {prefixes}\nGot:\n{responseStr.quote}"

def echoBodyHandler : TestHandler := fun req => do
  let body : String ← req.body.readAll
  Response.ok |>.text body

-- Baseline valid chunked request.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertContains "Chunked baseline status" response "HTTP/1.1 200 OK"
  assertContains "Chunked baseline body" response "hello"

-- Uppercase hex chunk-size.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\nA\x0d\n0123456789\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertContains "Chunk-size uppercase hex" response "HTTP/1.1 200 OK"
  assertContains "Chunk-size uppercase body" response "0123456789"

-- Leading zeros in chunk-size.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n0005\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertContains "Chunk-size leading zeros" response "HTTP/1.1 200 OK"
  assertContains "Chunk-size leading zeros body" response "hello"

-- Chunk extensions with token value.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5;ext=value\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertContains "Chunk extension token" response "HTTP/1.1 200 OK"

-- Chunk extensions with quoted value.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5;ext=\"quoted value\"\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertContains "Chunk extension quoted value" response "HTTP/1.1 200 OK"

-- Missing CRLF after chunk data should fail.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertStatusOneOf "Missing chunk-data CRLF" response #["HTTP/1.1 400", "HTTP/1.1 408"]

-- Invalid hex chunk-size should fail.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\nG\x0d\nhello\x0d\n0\x0d\n\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertStatusOneOf "Invalid hex chunk-size" response #["HTTP/1.1 400", "HTTP/1.1 408"]

-- Missing terminal zero-size chunk should fail.
#eval show IO _ from do
  let (client, server) ← Mock.new
  let raw := "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\n\x0d\n5\x0d\nhello\x0d\n".toUTF8
  let response ← sendRaw client server raw echoBodyHandler
  assertStatusOneOf "Missing terminal zero chunk" response #["HTTP/1.1 400", "HTTP/1.1 408"]
