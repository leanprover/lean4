import Std.Internal.Http
import Std.Internal.Async

open Std.Internal.IO.Async
open Std Http

structure Result where
  responseSent : Nat
  data : ByteArray

/-- Convert an HTTP request to a byte array, optionally using chunked encoding. -/
def toByteArray (req : Request (Array Chunk)) (chunked := false) : IO ByteArray := Async.block do
  let mut data := String.toUTF8 <| toString req.head
  let toByteArray (part : Chunk) := Internal.Encode.encode .v11 .empty part |>.toByteArray
  for part in req.body do data := data ++ (if chunked then toByteArray part else part.data)
  if chunked then data := data ++ toByteArray (Chunk.mk .empty .empty)
  return data

/-- Send multiple requests through a mock connection and return the response data. -/
def sendRequests (pair : Mock.Client × Mock.Server) (reqs : Array (Request (Array Chunk)))
    (onRequest : Request Body → Async (Response Body))
    (chunked : Bool := false) : IO ByteArray := Async.block do
  let (client, server) := pair
  let mut data := .empty
  for req in reqs do data := data ++ (← toByteArray req chunked)

  client.send data
  Std.Http.Server.serveConnection server onRequest (config := { lingeringTimeout := 3000 })

  let res ← client.recv?
  pure <| res.getD .empty

def testSizeLimit (pair : Mock.Client × Mock.Server) : IO Unit := do
  let handler := fun (req : Request Body) => do
    let mut size := 0
    for i in req.body do
      size := size + i.size
      if size > 10 then
        return Response.new
        |>.status .payloadTooLarge
        |>.header "Connection" (.new "close")
        |>.build

    return Response.new
      |>.status .ok
      |>.body "hello robert"

  let response ← sendRequests pair #[
     Request.new
      |>.uri! "/ata/po"
      |>.header "Content-Length" (.new "4")
      |>.header "Host" (.new ".")
      |>.body #[.mk "test".toUTF8 #[]],
    Request.new
      |>.uri! "/ata/po"
      |>.header "Content-Length" (.new "13")
      |>.header "Connection" (.new "close")
      |>.header "Host" (.new ".")
      |>.body #[.mk "testtesttests".toUTF8 #[]],
     Request.new
      |>.uri! "/ata/po"
      |>.header "Content-Length" (.new "4")
      |>.header "Host" (.new ".")
      |>.body #[.mk "test".toUTF8 #[]],
  ] handler

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
      |>.header "Custom-Header" (.new "test-value")
      |>.header "Connection" (.new "close")
      |>.body "Hello World"

  let response ← sendRequests pair #[
    Request.new
      |>.uri! "/hello"
      |>.header "Host" (.new "localhost")
      |>.header "User-Agent" (.new "TestClient/1.0")
      |>.header "Connection" (.new "close")
      |>.header "Content-Length" (.new "0")
      |>.method .get
      |>.body #[.mk "".toUTF8 #[]]
  ] handler

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
      |>.header "Content-Type" (.new "application/json")
      |>.header "Connection" (.new "close")
      |>.body s!"Received: {body}"

  let response ← sendRequests pair #[
    Request.new
      |>.uri! "/api/data"
      |>.method .post
      |>.header "Host" (.new "localhost")
      |>.header "Content-Type" (.new "application/json")
      |>.header "Content-Length" (.new "25")
      |>.header "Connection" (.new "close")
      |>.body #[.mk "{\"name\": \"test\", \"id\": 1}".toUTF8 #[]]
  ] handler

  let responseData := String.fromUTF8! response
  IO.println s!"{responseData.quote}"

def test100Continue : IO Unit := do
  let pair ← Mock.new

  let handler := fun (req : Request Body) => do
    let expectHeader := req.head.headers.getLast? "Expect" |>.getD (.new "")
    if expectHeader.is "100-continue" then
      return Response.new
        |>.status .continue
        |>.header "Connection" (.new "close")
        |>.build
    else
      return Response.new
        |>.status .ok
        |>.body "Request processed"

  let response ← sendRequests pair #[
    Request.new
      |>.uri! "/"
      |>.method .get
      |>.header "Host" (.new "example.com")
      |>.header "Content-Length" (.new "1")
      |>.header "Expect" (.new "100-continue")
      |>.header "Connection" (.new "close")
      |>.body #[.mk "a".toUTF8 #[]]
  ] handler

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
          |>.header "Content-Type" (.new "application/json")
          |>.header "Connection" (.new "close")
          |>.body "{\"error\": \"Request too large\", \"max_size\": 1000}"

    return Response.new
      |>.status .ok
      |>.body s!"Accepted request of size {totalSize}"

  let largeData :=
    Array.replicate 1500 97
    |> ByteArray.mk
    |> String.fromUTF8!

  let response ← sendRequests pair #[
    Request.new
      |>.uri! "/upload"
      |>.method .post
      |>.header "Host" (.new "localhost")
      |>.header "Content-Type" (.new "text/plain")
      |>.header "Content-Length" (.ofString! s!"{largeData.length}")
      |>.header "Connection" (.new "close")
      |>.body #[.mk largeData.toUTF8 #[]]
  ] handler

  let responseData := String.fromUTF8! response
  IO.println s!"{responseData.quote}"

/--
info: "HTTP/1.1 413 Request Entity Too Large\x0d\nContent-Length: 48\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\nContent-Type: application/json\x0d\n\x0d\n{\"error\": \"Request too large\", \"max_size\": 1000}"
-/
#guard_msgs in
#eval show IO _ from do testMaxRequestSize

def testCut : IO Unit := do
  let pair ← Mock.new

  let handler := fun (req : Request Body) => do
    if req.head.headers.hasEntry "Accept" "application/json" then
      return Response.new
        |>.status .accepted
        |>.header "Content-Type" (.new "application/json")
        |>.body "{\"message\": \"JSON response\", \"status\": \"accepted\"}"
    else if req.head.headers.hasEntry "Accept" "text/xml" then
      return Response.new
        |>.status .ok
        |>.header "Content-Type" (.new "application/xml")
        |>.body "<?xml version=\"1.0\"?><response><message>XML response</message></response>"
    else
      return Response.new
        |>.status .ok
        |>.header "Content-Type" (.new "text/plain")
        |>.body "Plain text response"

  let response ← sendRequests pair #[
    Request.new
      |>.uri! "/api/content"
      |>.method .post
      |>.header "Host" (.new "localhost")
      |>.header "Accept" (.new "application/json")
      |>.header "Content-Type" (.new "application/json")
      |>.header "Content-Length" (.new "18")
      |>.body #[.mk "{\"request\": \"data\"}".toUTF8 #[]],
    Request.new
      |>.uri! "/api/content"
      |>.method .get
      |>.header "Host" (.new "localhost")
      |>.header "Accept" (.new "text/xml")
      |>.header "Content-Length" (.new "1")
      |>.body #[.mk "a".toUTF8 #[]]
  ] handler

  let responseData := String.fromUTF8! response
  IO.println s!"{responseData.quote}"

/-
/--
info: "HTTP/1.1 202 Accepted\x0d\nContent-Length: 50\x0d\nServer: LeanHTTP/1.1\x0d\nContent-Type: application/json\x0d\n\x0d\n{\"message\": \"JSON response\", \"status\": \"accepted\"}HTTP/1.1 400 Bad Request\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval show IO _ from do testCut

/--
info: "HTTP/1.1 200 OK\x0d\nContent-Length: 35\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\nContent-Type: application/json\x0d\n\x0d\nReceived: {\"name\": \"test\", \"id\": 1}"
-/
#guard_msgs in
#eval show IO _ from do testPostRequest
-/

def testContentNegotiation : IO Unit := do
  let pair ← Mock.new

  let handler := fun (req : Request Body) => do
    if req.head.headers.hasEntry "Accept" "application/json" then
      return Response.new
        |>.status .accepted
        |>.header "Content-Type" (.new "application/json")
        |>.body "{\"message\": \"JSON response\", \"status\": \"accepted\"}"
    else if req.head.headers.hasEntry "Accept" "text/xml" then
      return Response.new
        |>.status .ok
        |>.header "Content-Type" (.new "application/xml")
        |>.body "<?xml version=\"1.0\"?><response><message>XML response</message></response>"
    else
      return Response.new
        |>.status .ok
        |>.header "Content-Type" (.new "text/plain")
        |>.body "Plain text response"

  let response ← sendRequests pair #[
    Request.new
      |>.uri! "/api/content"
      |>.method .post
      |>.header "Host" (.new "localhost")
      |>.header "Accept" (.new "application/json")
      |>.header "Content-Type" (.new "application/json")
      |>.header "Content-Length" (.new "19")
      |>.body #[.mk "{\"request\": \"data\"}".toUTF8 #[]],
    Request.new
      |>.uri! "/api/content"
      |>.method .get
      |>.header "Host" (.new "localhost")
      |>.header "Accept" (.new "text/xml")
      |>.header "Content-Length" (.new "1")
      |>.body #[.mk "a".toUTF8 #[]]
  ] handler

  let responseData := String.fromUTF8! response
  IO.println s!"{responseData.quote}"

/--
info: "HTTP/1.1 202 Accepted\x0d\nContent-Length: 50\x0d\nServer: LeanHTTP/1.1\x0d\nContent-Type: application/json\x0d\n\x0d\n{\"message\": \"JSON response\", \"status\": \"accepted\"}HTTP/1.1 200 OK\x0d\nContent-Length: 73\x0d\nServer: LeanHTTP/1.1\x0d\nContent-Type: application/xml\x0d\n\x0d\n<?xml version=\"1.0\"?><response><message>XML response</message></response>"
-/
#guard_msgs in
#eval show IO _ from do testContentNegotiation

def testContentNegotiationError : IO Unit := do
  let pair ← Mock.new

  let handler := fun (req : Request Body) => do
    if req.head.headers.hasEntry "Accept" "application/json" then
      return Response.new
        |>.status .accepted
        |>.header "Content-Type" (.new "application/json")
        |>.body "{\"message\": \"JSON response\", \"status\": \"accepted\"}"
    else if req.head.headers.hasEntry "Accept" "text/xml" then
      return Response.new
        |>.status .ok
        |>.header "Content-Type" (.new "application/xml")
        |>.body "<?xml version=\"1.0\"?><response><message>XML response</message></response>"
    else
      return Response.new
        |>.status .ok
        |>.header "Content-Type" (.new "text/plain")
        |>.body "Plain text response"

  let response ← sendRequests pair #[
    Request.new
      |>.uri! "/api/content"
      |>.method .post
      |>.header "Host" (.new "localhost")
      |>.header "Accept" (.new "application/json")
      |>.header "Content-Type" (.new "application/json")
      |>.header "Content-Length" (.new "18")
      |>.body #[.mk "{\"request\": \"data\"}".toUTF8 #[]],
    Request.new
      |>.uri! "/api/content"
      |>.method .get
      |>.header "Host" (.new "localhost")
      |>.header "Accept" (.new "text/xml")
      |>.header "Content-Length" (.new "1")
      |>.body #[.mk "a".toUTF8 #[]]
  ] handler

  let responseData := String.fromUTF8! response
  IO.println s!"{responseData.quote}"

/--
info: "HTTP/1.1 202 Accepted\x0d\nContent-Length: 50\x0d\nServer: LeanHTTP/1.1\x0d\nContent-Type: application/json\x0d\n\x0d\n{\"message\": \"JSON response\", \"status\": \"accepted\"}HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval show IO _ from do testContentNegotiationError
