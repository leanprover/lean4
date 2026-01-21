/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
import Std.Internal.Http
import Std.Internal.Async

open Std.Internal.IO.Async
open Std Http

/-!
# HTTP Server Tests

Comprehensive tests for HTTP server compliance, security, and request handling.
Tests raw byte handling, request smuggling prevention, and protocol compliance.
-/

-- ============================================================================
-- Helper Functions
-- ============================================================================

def requestToByteArray (req : Request (Array Chunk)) (chunked := false) : IO ByteArray := Async.block do
  let mut data := String.toUTF8 <| toString req.head
  let toByteArray (part : Chunk) := Internal.Encode.encode .v11 .empty part |>.toByteArray
  for part in req.body do data := data ++ (if chunked then toByteArray part else part.data)
  if chunked then data := data ++ toByteArray (Chunk.mk .empty .empty)
  return data

def sendRawBytes (data : Array ByteArray)
    (onRequest : Request Body → ContextAsync (Response Body))
    (config : Config := { lingeringTimeout := 3000 }) : IO ByteArray := Async.block do
  let (client, server) ← Mock.new
  for d in data do
    client.send d
  client.close
  Std.Http.Server.serveConnection server onRequest (fun _ => pure ()) config |>.run
  let res ← client.recv?
  pure <| res.getD .empty

def echoHandler (req: Request Body) : ContextAsync (Response Body) := do
  let mut data := ByteArray.empty
  for chunk in req.body do
    data := data ++ chunk.data
  return Response.new
    |>.status .ok
    |>.body data

def maximumSizeHandlerEcho (maxSize : Nat) (req: Request Body) : ContextAsync (Response Body) := do
  let mut size := 0
  let mut data := ByteArray.empty
  for i in req.body do
    size := size + i.size
    data := data ++ i.data
    if size > maxSize then
      return Response.new
        |>.status .payloadTooLarge
        |>.header! "Connection" "close"
        |>.body .empty
  return Response.new
    |>.status .ok
    |>.body data

-- ============================================================================
-- Fragmented Request Tests
-- ============================================================================

/--
info: "HTTP/1.1 200 OK\x0d\nContent-Length: 1\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\na"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST /ata/po HTTP/1.1\r\nCont".toUTF8, "ent-Length: 1\r\nHost: ata\r\n\r\na".toUTF8] (maximumSizeHandlerEcho 150)
  IO.println <| String.quote <| String.fromUTF8! response

/--
info: "HTTP/1.1 200 OK\x0d\nContent-Length: 5\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nhello"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["PO".toUTF8, "ST / HTTP/1.1\r\nContent-Length: 5\r\nHost: test\r\n\r\nhello".toUTF8] (maximumSizeHandlerEcho 150)
  IO.println <| String.quote <| String.fromUTF8! response

/--
info: "HTTP/1.1 200 OK\x0d\nContent-Length: 4\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\ntest"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST /path/to/".toUTF8, "resource HTTP/1.1\r\nContent-Length: 4\r\nHost: test\r\n\r\ntest".toUTF8] (maximumSizeHandlerEcho 150)
  IO.println <| String.quote <| String.fromUTF8! response

/--
info: "HTTP/1.1 200 OK\x0d\nContent-Length: 10\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nhelloworld"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST / HTTP/1.1\r\nContent-Length: 10\r\nHost: test\r\n\r\nhello".toUTF8, "world".toUTF8] (maximumSizeHandlerEcho 150)
  IO.println <| String.quote <| String.fromUTF8! response

/--
info: "HTTP/1.1 200 OK\x0d\nContent-Length: 2\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nok"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["P".toUTF8, "O".toUTF8, "ST / HTTP/1.1\r\nContent-Length: 2\r\nHost: test\r\n\r\n".toUTF8, "o".toUTF8, "k".toUTF8] (maximumSizeHandlerEcho 150)
  IO.println <| String.quote <| String.fromUTF8! response

-- ============================================================================
-- Basic HTTP Methods
-- ============================================================================

/--
info: "HTTP/1.1 200 OK\x0d\nContent-Length: 0\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["GET / HTTP/1.1\r\nHost: test\r\n\r\n".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response

/--
info: "HTTP/1.1 200 OK\x0d\nContent-Length: 0\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST / HTTP/1.1\r\nContent-Length: 0\r\nHost: test\r\n\r\n".toUTF8] (maximumSizeHandlerEcho 150)
  IO.println <| String.quote <| String.fromUTF8! response

-- ============================================================================
-- Chunked Encoding Tests
-- ============================================================================

/--
info: "HTTP/1.1 200 OK\x0d\nContent-Length: 11\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nhello world"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST / HTTP/1.1\r\nTransfer-Encoding: chunked\r\nHost: test\r\n\r\n5\r\nhello\r\n6\r\n world\r\n0\r\n\r\n".toUTF8] (maximumSizeHandlerEcho 150)
  IO.println <| String.quote <| String.fromUTF8! response

/--
info: "HTTP/1.1 200 OK\x0d\nContent-Length: 4\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\ntest"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST / HTTP/1.1\r\nTransfer-Encoding: chunked\r\nHost: test\r\n\r\n4;ext=value\r\ntest\r\n0\r\n\r\n".toUTF8] (maximumSizeHandlerEcho 150)
  IO.println <| String.quote <| String.fromUTF8! response

/--
info: "HTTP/1.1 200 OK\x0d\nContent-Length: 3\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nfoo"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST / HTTP/1.1\r\nTransfer-Encoding: chunked\r\nHost: test\r\n\r\n3\r\nfoo\r\n0\r\nX-Trailer: value\r\n\r\n".toUTF8] (maximumSizeHandlerEcho 150)
  IO.println <| String.quote <| String.fromUTF8! response

/--
info: "HTTP/1.1 200 OK\x0d\nContent-Length: 0\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST / HTTP/1.1\r\nTransfer-Encoding: chunked\r\nHost: test\r\n\r\n0\r\n\r\n".toUTF8] (maximumSizeHandlerEcho 150)
  IO.println <| String.quote <| String.fromUTF8! response

/--
info: "HTTP/1.1 200 OK\x0d\nContent-Length: 5\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nhello"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST / HTTP/1.1\r\nTransfer-Encoding: gzip, chunked\r\nHost: test\r\n\r\n5\r\nhello\r\n0\r\n\r\n".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response

-- ============================================================================
-- CL.CL Attack Prevention (Duplicate Content-Length)
-- ============================================================================

/--
info: "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST / HTTP/1.1\r\nContent-Length: 5\r\nContent-Length: 5\r\nHost: test\r\n\r\nhello".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response

/--
info: "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST / HTTP/1.1\r\nContent-Length: 5\r\nContent-Length: 10\r\nHost: test\r\n\r\nhello".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response

/--
info: "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST / HTTP/1.1\r\nContent-Length: 5, 10\r\nHost: test\r\n\r\nhello".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response

-- ============================================================================
-- CL.TE Attack Prevention (Content-Length + Transfer-Encoding)
-- ============================================================================

/--
info: "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST / HTTP/1.1\r\nContent-Length: 100\r\nTransfer-Encoding: chunked\r\nHost: test\r\n\r\n5\r\nhello\r\n0\r\n\r\n".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response

/--
info: "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST / HTTP/1.1\r\nTransfer-Encoding: chunked\r\nContent-Length: 100\r\nHost: test\r\n\r\n5\r\nhello\r\n0\r\n\r\n".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response

-- ============================================================================
-- Transfer-Encoding Validation
-- ============================================================================

/--
info: "HTTP/1.1 200 OK\x0d\nContent-Length: 5\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nhello"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST / HTTP/1.1\r\nTransfer-Encoding: chunked\r\nTransfer-Encoding: chunked\r\nHost: test\r\n\r\n5\r\nhello\r\n0\r\n\r\n".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response

-- ============================================================================
-- Invalid Methods
-- ============================================================================

/--
info: "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["INVALID / HTTP/1.1\r\nHost: test\r\n\r\n".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response

/--
info: "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["get / HTTP/1.1\r\nHost: test\r\n\r\n".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response

-- ============================================================================
-- Invalid HTTP Versions
-- ============================================================================

/--
info: "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["GET / HTTP/1.0\r\nHost: test\r\n\r\n".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response

/--
info: "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["GET / HTTP/2.0\r\nHost: test\r\n\r\n".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response

-- ============================================================================
-- Missing Host Header
-- ============================================================================

/--
info: "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["GET / HTTP/1.1\r\n\r\n".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response

-- ============================================================================
-- Malformed Request Line
-- ============================================================================

/--
info: "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["GET /\r\nHost: test\r\n\r\n".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response

-- ============================================================================
-- Header Injection Prevention
-- ============================================================================

/--
info: "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST / HTTP/1.1\r\nX-Custom".toUTF8, ByteArray.mk #[0], ": value\r\nHost: test\r\n\r\n".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response

/--
info: "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST / HTTP/1.1\r\nX-Custom\t: value\r\nHost: test\r\n\r\n".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response

/--
info: "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST / HTTP/1.1\r\nX-Custom : value\r\nHost: test\r\n\r\n".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response

/--
info: "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST / HTTP/1.1\r\n: value\r\nHost: test\r\n\r\n".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response

/--
info: "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST / HTTP/1.1\r\nInvalid Header: value\r\nHost: test\r\n\r\n".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response

-- ============================================================================
-- Invalid Chunked Encoding
-- ============================================================================

/--
info: "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST / HTTP/1.1\r\nTransfer-Encoding: chunked\r\nHost: test\r\n\r\nZZZ\r\ndata\r\n0\r\n\r\n".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response

/--
info: "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST / HTTP/1.1\r\nTransfer-Encoding: chunked\r\nHost: test\r\n\r\n5hello\r\n0\r\n\r\n".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response

/--
info: "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST / HTTP/1.1\r\nTransfer-Encoding: chunked\r\nHost: test\r\n\r\n5\r\nhello\r\n".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response

/--
info: "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST / HTTP/1.1\r\nTransfer-Encoding: chunked\r\nHost: test\r\n\r\nA\r\nhello\r\n0\r\n\r\n".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response

-- ============================================================================
-- Content-Length Validation
-- ============================================================================

/--
info: "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST / HTTP/1.1\r\nContent-Length: -5\r\nHost: test\r\n\r\n".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response

/--
info: "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST / HTTP/1.1\r\nContent-Length: abc\r\nHost: test\r\n\r\n".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response

/--
info: "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST / HTTP/1.1\r\nContent-Length: 100\r\nHost: test\r\n\r\nshort".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response

/--
info: "HTTP/1.1 200 OK\x0d\nContent-Length: 5\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nhello"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST / HTTP/1.1\r\nContent-Length: 5\r\nHost: test\r\n\r\nhello".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response

/--
info: "HTTP/1.1 200 OK\x0d\nContent-Length: 5\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nexact"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST / HTTP/1.1\r\nContent-Length: 5\r\nHost: test\r\n\r\nexact".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response

-- ============================================================================
-- Keep-Alive / Pipelining Tests
-- ============================================================================

/--
info: "HTTP/1.1 200 OK\x0d\nContent-Length: 5\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nfirstHTTP/1.1 200 OK\x0d\nContent-Length: 6\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nsecond"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST / HTTP/1.1\r\nContent-Length: 5\r\nHost: test\r\n\r\nfirstPOST / HTTP/1.1\r\nContent-Length: 6\r\nHost: test\r\n\r\nsecond".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response

/--
info: "HTTP/1.1 200 OK\x0d\nContent-Length: 4\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\ndata"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST / HTTP/1.1\r\nContent-Length: 4\r\nConnection: close\r\nHost: test\r\n\r\ndata".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response

/--
info: "HTTP/1.1 200 OK\x0d\nContent-Length: 9\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nkeepalive"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST / HTTP/1.1\r\nContent-Length: 9\r\nConnection: keep-alive\r\nHost: test\r\n\r\nkeepalive".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response

-- ============================================================================
-- Multiple Headers
-- ============================================================================

/--
info: "HTTP/1.1 200 OK\x0d\nContent-Length: 4\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\ndata"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST / HTTP/1.1\r\nContent-Length: 4\r\nX-Custom: value1\r\nX-Custom: value2\r\nHost: test\r\n\r\ndata".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response

/--
info: "HTTP/1.1 200 OK\x0d\nContent-Length: 2\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nok"
-/
#guard_msgs in
#eval show IO Unit from do
  let longValue := String.join (List.replicate 1000 "x")
  let response ← sendRawBytes #[s!"POST / HTTP/1.1\r\nX-Long: {longValue}\r\nContent-Length: 2\r\nHost: test\r\n\r\nok".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response

-- ============================================================================
-- Extra Data After Body
-- ============================================================================

/--
info: "HTTP/1.1 200 OK\x0d\nContent-Length: 5\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nhelloHTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST / HTTP/1.1\r\nContent-Length: 5\r\nHost: test\r\n\r\nhello extra data here".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response

-- ============================================================================
-- Header Folding (Obsolete, should be rejected)
-- ============================================================================

/--
info: "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST / HTTP/1.1\r\nContent-Length:   5   \r\nHost: test\r\n\r\nhello".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response

/--
info: "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST / HTTP/1.1\r\nX-Custom: line1\r\n continuation\r\nHost: test\r\n\r\n".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response

-- ============================================================================
-- Control Characters in Path
-- ============================================================================

/--
info: "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval show IO Unit from do
  let response ← sendRawBytes #["POST /path\x0Btest HTTP/1.1\r\nHost: test\r\n\r\n".toUTF8] echoHandler
  IO.println <| String.quote <| String.fromUTF8! response
