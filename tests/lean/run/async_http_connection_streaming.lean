import Std.Internal.Http
import Std.Internal.Async

open Std.Internal.IO.Async
open Std Http

structure TestCase where
  /-- Descriptive name for the test -/
  name : String
  /-- The HTTP request to send -/
  request : Request (Array Chunk)
  /-- Handler function to process the request -/
  handler : Request Body → ContextAsync (Response Body)
  /-- Expected response string -/
  expected : String
  /-- Whether to use chunked encoding -/
  chunked : Bool := false
  deriving Inhabited

/-- Convert an HTTP request to a byte array, optionally using chunked encoding. -/
def toByteArray (req : Request (Array Chunk)) (chunked := false) : IO ByteArray := Async.block do
  let mut data := String.toUTF8 <| toString req.head
  let toByteArray (part : Chunk) := Internal.Encode.encode .v11 .empty part |>.toByteArray
  for part in req.body do data := data ++ (if chunked then toByteArray part else part.data)
  if chunked then data := data ++ toByteArray (Chunk.mk .empty .empty)
  return data

/-- Send multiple requests through a mock connection and return the response data. -/
def sendRequests (client : Mock.Client) (server : Mock.Server) (reqs : Array (Request (Array Chunk)))
    (onRequest : Request Body → ContextAsync (Response Body))
    (chunked : Bool := false) : IO ByteArray := Async.block do
  let mut data := .empty
  for req in reqs do data := data ++ (← toByteArray req chunked)

  client.send data
  Std.Http.Server.serveConnection server onRequest (config := { lingeringTimeout := 3000 })
  |>.run (← Context.new)

  let res ← client.recv?
  pure <| res.getD .empty

/-- Run a single test case, comparing actual response against expected response. -/
def runTest (name : String) (client : Mock.Client) (server : Mock.Server) (req : Request (Array Chunk))
    (handler : Request Body → ContextAsync (Response Body)) (expected : String) (chunked : Bool := false) :
    IO Unit := do
  let response ← sendRequests client server #[req] handler chunked
  let responseData := String.fromUTF8! response

  if responseData != expected then
    throw <| IO.userError s!
      "Test '{name}' failed:\n\
       Expected:\n{expected}\n\
       Got:\n{responseData}"

def runTestCase (tc : TestCase) : IO Unit := do
  let (client, server) ← Mock.new
  runTest tc.name client server tc.request tc.handler tc.expected tc.chunked

-- Request Predicates

/-- Check if request is a basic GET requests to the specified URI and host. -/
def isBasicGetRequest (req : Request Body) (uri : String) (host : String) : Bool :=
  req.head.method == .get ∧
  req.head.version == .v11 ∧
  toString req.head.uri = uri ∧
  req.head.headers.hasEntry (.new "Host") host

/-- Check if request has a specific Content-Length header. -/
def hasContentLength (req : Request Body) (length : String) : Bool :=
  req.head.headers.hasEntry (.new "Content-Length") length

/-- Check if request uses chunked transfer encoding. -/
def isChunkedRequest (req : Request Body) : Bool :=
  req.head.headers.hasEntry (.new "Transfer-Encoding") "chunked"

/-- Check if request has a specific header with a specific value. -/
def hasHeader (req : Request Body) (name : String) (value : String) : Bool :=
  if let some name := HeaderName.ofString? name then
    req.head.headers.hasEntry name value
  else
    false

/-- Check if request method matches the expected method. -/
def hasMethod (req : Request Body) (method : Method) : Bool :=
  req.head.method == method

/-- Check if request URI matches the expected URI string. -/
def hasUri (req : Request Body) (uri : String) : Bool :=
  toString req.head.uri = uri

-- Tests

#eval runTestCase {
  name := "Streaming response with fixed Content-Length"

  request := Request.new
    |>.method .get
    |>.uri! "/stream"
    |>.header! "Host" "example.com"
    |>.header! "Connection" "close"
    |>.body #[]

  handler := fun req => do
    let stream ← Body.ByteStream.empty

    background do
      for i in [0:3] do
        let sleep ← Sleep.mk 5
        sleep.wait
        discard <| stream.write s!"chunk{i}\n".toUTF8
      stream.close

    return Response.ok stream (.empty |>.insert (.new "Content-Length") (.new "21"))

  expected := "HTTP/1.1 200 OK\x0d\nContent-Length: 21\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nchunk0\nchunk1\nchunk2\n"
}

#eval runTestCase {
  name := "Streaming response with setKnownSize fixed"

  request := Request.new
    |>.method .get
    |>.uri! "/stream-sized"
    |>.header! "Host" "example.com"
    |>.header! "Connection" "close"
    |>.body #[]

  handler := fun _ => do
    let stream ← Body.ByteStream.empty
    stream.setKnownSize (some (.fixed 15))

    background do
      for i in [0:3] do
        discard <| stream.write s!"data{i}".toUTF8

      stream.close

    return Response.ok stream .empty

  expected := "HTTP/1.1 200 OK\x0d\nContent-Length: 15\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\ndata0data1data2"
}

#eval runTestCase {
  name := "Streaming response with chunked encoding"

  request := Request.new
    |>.method .get
    |>.uri! "/stream-chunked"
    |>.header! "Host" "example.com"
    |>.header! "Connection" "close"
    |>.body #[]

  handler := fun _ => do
    let stream ← Body.ByteStream.empty

    background do
      discard <| stream.write "hello".toUTF8
      discard <| stream.write "world".toUTF8
      stream.close
    return Response.ok stream .empty

  expected := "HTTP/1.1 200 OK\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n5\x0d\nhello\x0d\n5\x0d\nworld\x0d\n0\x0d\n\x0d\n"
}

#eval runTestCase {
  name := "Chunked request with streaming response"

  request := Request.new
    |>.method .post
    |>.uri! "/"
    |>.header! "Host" "example.com"
    |>.header! "Transfer-Encoding" "chunked"
    |>.header! "Connection" "close"
    |>.body #[
      .mk "data1".toUTF8 #[],
      .mk "data2".toUTF8 #[]
    ]

  handler := fun req => do
    if isChunkedRequest req
    then
      let stream ← Body.ByteStream.empty
      background do
        for i in [0:2] do
          discard <| stream.write s!"response{i}".toUTF8
        stream.close
      return Response.ok stream (.empty |>.insert (.new "Content-Length") (.new "18"))
    else
      return Response.badRequest "not chunked"

  expected := "HTTP/1.1 200 OK\x0d\nContent-Length: 18\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nresponse0response1"
  chunked := true
}

#eval runTestCase {
  name := "Chunked request with streaming response"

  request := Request.new
    |>.method .post
    |>.uri! "/"
    |>.header! "Host" "example.com"
    |>.header! "Transfer-Encoding" "chunked"
    |>.header! "Connection" "close"
    |>.body #[
      .mk "data1".toUTF8 #[],
      .mk "data2".toUTF8 #[]
    ]

  handler := fun req => do
    if isChunkedRequest req
    then
      let stream ← Body.ByteStream.empty
      background do
        for i in [0:2] do
          discard <| stream.write s!"response{i}".toUTF8
        stream.close
      return Response.ok stream (.empty |>.insert (.new "Content-Length") (.new "18"))
    else
      return Response.badRequest "not chunked"

  expected := "HTTP/1.1 200 OK\x0d\nContent-Length: 18\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nresponse0response1"
  chunked := true
}
