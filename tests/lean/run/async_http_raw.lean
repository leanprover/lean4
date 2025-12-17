import Std.Internal.Http
import Std.Internal.Async

open Std.Internal.IO.Async
open Std Http

structure Result where
  responseSent : Nat
  data : ByteArray

/-- Convert an HTTP request to a byte array, optionally using chunked encoding. -/
def requestToByteArray (req : Request (Array Chunk)) (chunked := false) : IO ByteArray := Async.block do
  let mut data := String.toUTF8 <| toString req.head
  let toByteArray (part : Chunk) := Internal.Encode.encode .v11 .empty part |>.toByteArray
  for part in req.body do data := data ++ (if chunked then toByteArray part else part.data)
  if chunked then data := data ++ toByteArray (Chunk.mk .empty .empty)
  return data

/-- Send raw byte stream through a mock connection and return the response data. -/
def sendRawBytes (pair : Mock.Client × Mock.Server) (data : ByteArray)
    (onRequest : Request Body → ContextAsync (Response Body)) (config : Config := { lingeringTimeout := 3000 }) : IO ByteArray := Async.block do
  let (client, server) := pair

  client.send data
  Std.Http.Server.serveConnection server onRequest config
  |>.runIn (← CancellationContext.new)

  let res ← client.recv?
  pure <| res.getD .empty

def testSizeLimit (pair : Mock.Client × Mock.Server) : IO Unit := do
  let handler : Request Body → ContextAsync (Response Body) := fun (req : Request Body) => do
    let mut size := 0
    for i in req.body do
      size := size + i.size
      if size > 10 then
        return Response.new
        |>.status .payloadTooLarge
        |>.header! "Connection" "close"
        |>.body .zero

    return Response.new
      |>.status .ok
      |>.body "hello robert"

  -- Manually construct the byte stream
  let mut data := .empty
  data := data ++ (← requestToByteArray (
     Request.new
      |>.uri! "/ata/po"
      |>.header! "Content-Length" "4"
      |>.header! "Host" "."
      |>.body #[.mk "test".toUTF8 #[]]))
  data := data ++ (← requestToByteArray (
    Request.new
      |>.uri! "/ata/po"
      |>.header! "Content-Length" "13"
      |>.header! "Connection" "close"
      |>.header! "Host" "."
      |>.body #[.mk "testtesttests".toUTF8 #[]]))
  data := data ++ (← requestToByteArray (
     Request.new
      |>.uri! "/ata/po"
      |>.header! "Content-Length" "4"
      |>.header! "Host" "."
      |>.body #[.mk "test".toUTF8 #[]]))

  let response ← sendRawBytes pair data handler

  let responseData := String.fromUTF8! response
  IO.println <| String.quote responseData

/--
info: "HTTP/1.1 200 OK\x0d\nContent-Length: 12\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nhello robertHTTP/1.1 413 Request Entity Too Large\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval show IO _ from do testSizeLimit (← Mock.new)

def testBasicRequest : IO Unit := do
  let pair ← Mock.new

  let handler := fun (_ : Request Body) => do
    return Response.new
      |>.status .ok
      |>.header! "Custom-Header" "test-value"
      |>.header! "Connection" "close"
      |>.body "Hello World"

  let data ← requestToByteArray (
    Request.new
      |>.uri! "/hello"
      |>.header! "Host" "localhost"
      |>.header! "User-Agent" "TestClient/1.0"
      |>.header! "Connection" "close"
      |>.header! "Content-Length" "0"
      |>.method .get
      |>.body #[.mk "".toUTF8 #[]])

  let response ← sendRawBytes pair data handler

  let responseData := String.fromUTF8! response
  IO.println s!"{responseData.quote}"

/--
info: "HTTP/1.1 200 OK\x0d\nContent-Length: 11\x0d\nConnection: close\x0d\nCustom-Header: test-value\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nHello World"
-/
#guard_msgs in
#eval show IO _ from do testBasicRequest

def testPostRequest : IO Unit := do
  let pair ← Mock.new

  let handler := fun (req : Request Body) => do
    let mut body := ""
    for chunk in req.body do
      body := body ++ String.fromUTF8! chunk.data

    return Response.new
      |>.status .ok
      |>.header! "Content-Type" "application/json"
      |>.header! "Connection" "close"
      |>.body s!"Received: {body}"

  let data ← requestToByteArray (
    Request.new
      |>.uri! "/api/data"
      |>.method .post
      |>.header! "Host" "localhost"
      |>.header! "Content-Type" "application/json"
      |>.header! "Content-Length" "25"
      |>.header! "Connection" "close"
      |>.body #[.mk "{\"name\": \"test\", \"id\": 1}".toUTF8 #[]])

  let response ← sendRawBytes pair data handler

  let responseData := String.fromUTF8! response
  IO.println s!"{responseData.quote}"

def test100Continue : IO Unit := do
  let pair ← Mock.new

  let handler := fun (req : Request Body) => do
    let expectHeader := req.head.headers.getLast? (.new "Expect") |>.getD (.new "")
    if expectHeader.is "100-continue" then
      return Response.new
        |>.status .continue
        |>.header! "Connection" "close"
        |>.body Body.zero
    else
      return Response.new
        |>.status .ok
        |>.body "Request processed"

  let data ← requestToByteArray (
    Request.new
      |>.uri! "/"
      |>.method .get
      |>.header! "Host" "example.com"
      |>.header! "Content-Length" "1"
      |>.header! "Expect" "100-continue"
      |>.header! "Connection" "close"
      |>.body #[.mk "a".toUTF8 #[]])

  let response ← sendRawBytes pair data handler

  let responseData := String.fromUTF8! response
  IO.println s!"{responseData.quote}"

/--
info: "HTTP/1.1 100 Continue\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval show IO _ from do test100Continue

def testMaxRequestSize : IO Unit := do
  let pair ← Mock.new

  let handler := fun (req : Request Body) => do
    let mut totalSize := 0
    for chunk in req.body do
      totalSize := totalSize + chunk.size
      if totalSize > 1000 then
        return Response.new
          |>.status .payloadTooLarge
          |>.header! "Content-Type" "application/json"
          |>.header! "Connection" "close"
          |>.body "{\"error\": \"Request too large\", \"max_size\": 1000}"

    return Response.new
      |>.status .ok
      |>.body s!"Accepted request of size {totalSize}"

  let largeData :=
    Array.replicate 1500 97
    |> ByteArray.mk
    |> String.fromUTF8!

  let data ← requestToByteArray (
    Request.new
      |>.uri! "/upload"
      |>.method .post
      |>.header! "Host" "localhost"
      |>.header! "Content-Type" "text/plain"
      |>.header! "Content-Length" s!"{largeData.length}"
      |>.header! "Connection" "close"
      |>.body #[.mk largeData.toUTF8 #[]])

  let response ← sendRawBytes pair data handler

  let responseData := String.fromUTF8! response
  IO.println s!"{responseData.quote}"

/--
info: "HTTP/1.1 413 Request Entity Too Large\x0d\nContent-Length: 48\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\nContent-Type: application/json\x0d\n\x0d\n{\"error\": \"Request too large\", \"max_size\": 1000}"
-/
#guard_msgs in
#eval show IO _ from do testMaxRequestSize

def testChunkedWithTrailer : IO Unit := do
  let pair ← Mock.new

  let handler := fun (req : Request Body) => do
    let mut body := ""
    for chunk in req.body do
      body := body ++ String.fromUTF8! chunk.data

    let checksum := req.head.headers.getLast? (.new "X-Checksum") |>.map (·.value) |>.getD ""

    return Response.new
      |>.status .ok
      |>.header! "Content-Type" "text/plain"
      |>.header! "Connection" "close"
      |>.body s!"hello: {body.quote}."

  -- Construct raw ByteArray for chunked request with trailer
  -- This cannot be done with Request builder since it doesn't support trailers
  let rawRequest := "POST / HTTP/1.1\r\nHost: localhost\r\nUser-Agent: TestClient/1.0\r\nTransfer-Encoding: chunked\r\nTrailer: X-Checksum\r\nAccept: */*\r\n\r\n5\r\nHello\r\n6\r\n World\r\n0\r\nX-Checksum: abcd\r\n\r\n"
  let data : ByteArray := rawRequest.toUTF8

  let response ← sendRawBytes pair data handler

  let responseData := String.fromUTF8! response
  IO.println s!"{responseData.quote}"

/--
info: "HTTP/1.1 200 OK\x0d\nContent-Length: 21\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\nContent-Type: text/plain\x0d\n\x0d\nhello: \"Hello World\"."
-/
#guard_msgs in
#eval show IO _ from do testChunkedWithTrailer

def testContentNegotiation : IO Unit := do
  let pair ← Mock.new

  let handler := fun (req : Request Body) => do
    if req.head.headers.hasEntry (.new "Accept") "application/json" then
      return Response.new
        |>.status .accepted
        |>.header! "Content-Type" "application/json"
        |>.body "{\"message\": \"JSON response\", \"status\": \"accepted\"}"
    else if req.head.headers.hasEntry (.new "Accept") "text/xml" then
      return Response.new
        |>.status .ok
        |>.header! "Content-Type" "application/xml"
        |>.body "<?xml version=\"1.0\"?><response><message>XML response</message></response>"
    else
      return Response.new
        |>.status .ok
        |>.header! "Content-Type" "text/plain"
        |>.body "Plain text response"

  let mut data := .empty

  data := data ++ (← requestToByteArray (
    Request.new
      |>.uri! "/api/content"
      |>.method .post
      |>.header! "Host" "localhost"
      |>.header! "Accept" "application/json"
      |>.header! "Content-Type" "application/json"
      |>.header! "Content-Length" "19"
      |>.body #[.mk "{\"request\": \"data\"}".toUTF8 #[]]))

  data := data ++ (← requestToByteArray (
    Request.new
      |>.uri! "/api/content"
      |>.method .get
      |>.header! "Host" "localhost"
      |>.header! "Accept" "text/xml"
      |>.header! "Content-Length" "1"
      |>.body #[.mk "a".toUTF8 #[]]))

  let response ← sendRawBytes pair data handler

  let responseData := String.fromUTF8! response
  IO.println s!"{responseData.quote}"

def test20Requests : IO Unit := do
  let pair ← Mock.new

  let handler := fun (_ : Request Body) => do
    return Response.new
      |>.status .ok
      |>.header! "Content-Type" "text/plain"
      |>.body "OK"

  -- Build 20 identical requests
  let mut data := .empty
  for _ in [0:20] do
    data := data ++ (← requestToByteArray (
      Request.new
        |>.uri! "/test"
        |>.method .get
        |>.header! "Host" "localhost"
        |>.header! "User-Agent" "TestClient/1.0"
        |>.header! "Content-Length" "0"
        |>.body #[.mk "".toUTF8 #[]]))

  -- Add Connection: close to the last request
  data := data ++ (← requestToByteArray (
    Request.new
      |>.uri! "/test"
      |>.method .get
      |>.header! "Host" "localhost"
      |>.header! "User-Agent" "TestClient/1.0"
      |>.header! "Connection" "close"
      |>.header! "Content-Length" "0"
      |>.body #[.mk "".toUTF8 #[]]))

  let response ← sendRawBytes pair data handler { lingeringTimeout := 2000, maxRequests := 10 }

  let responseData := String.fromUTF8! response
  let responseCount := (responseData.splitOn "HTTP/1.1 200 OK").length - 1
  IO.println s!"Sent 21 requests, received {responseCount} responses"

/--
info: Sent 21 requests, received 10 responses
-/
#guard_msgs in
#eval show IO _ from do test20Requests

def testKeepAlive : IO Unit := do
  let pair ← Mock.new

  let handler := fun (_ : Request Body) => do
    return Response.new
      |>.status .ok
      |>.header! "Content-Type" "text/plain"
      |>.body "OK"

  -- Build 20 identical requests
  let mut data := .empty
  for _ in [0:20] do
    data := data ++ (← requestToByteArray (
      Request.new
        |>.uri! "/test"
        |>.method .get
        |>.header! "Host" "localhost"
        |>.header! "User-Agent" "TestClient/1.0"
        |>.header! "Content-Length" "0"
        |>.body #[.mk "".toUTF8 #[]]))

  -- Add Connection: close to the last request
  data := data ++ (← requestToByteArray (
    Request.new
      |>.uri! "/test"
      |>.method .get
      |>.header! "Host" "localhost"
      |>.header! "User-Agent" "TestClient/1.0"
      |>.header! "Connection" "close"
      |>.header! "Content-Length" "0"
      |>.body #[.mk "".toUTF8 #[]]))

  let response ← sendRawBytes pair data handler { lingeringTimeout := 2000, maxRequests := 10, enableKeepAlive := false }

  let responseData := String.fromUTF8! response
  let responseCount := (responseData.splitOn "HTTP/1.1 200 OK").length - 1
  IO.println s!"Sent 21 requests, received {responseCount} responses"

/--
info: Sent 21 requests, received 1 responses
-/
#guard_msgs in
#eval show IO _ from do testKeepAlive
