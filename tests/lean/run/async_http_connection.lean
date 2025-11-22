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
  handler : Request Body → Async (Response Body)
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
    (onRequest : Request Body → Async (Response Body))
    (chunked : Bool := false) : IO ByteArray := Async.block do
  let mut data := .empty
  for req in reqs do data := data ++ (← toByteArray req chunked)

  client.send data
  Std.Http.Server.serveConnection server onRequest (config := { lingeringTimeout := 3000 })

  let res ← client.recv?
  pure <| res.getD .empty

/-- Run a single test case, comparing actual response against expected response. -/
def runTest (name : String) (client : Mock.Client) (server : Mock.Server) (req : Request (Array Chunk))
    (handler : Request Body → Async (Response Body)) (expected : String) (chunked : Bool := false) :
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

/-- Check if request is a basic GET request to the specified URI and host. -/
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
  name := "GET with Content-Length"

  request := Request.new
    |>.method .get
    |>.uri! "/"
    |>.header! "Host" "example.com"
    |>.header! "Content-Length" "7"
    |>.body #[.mk "survive".toUTF8 #[]]

  handler := fun req => do
    if isBasicGetRequest req "/" "example.com" ∧ hasContentLength req "7"
    then return Response.ok "ok"
    else return Response.badRequest "invalid"

  expected := "HTTP/1.1 200 OK\x0d\nContent-Length: 2\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nok"
}

#eval runTestCase {
  name := "Simple GET request"

  request := Request.new
    |>.method .get
    |>.uri! "/api/users"
    |>.header! "Host" "api.example.com"
    |>.body #[]

  handler := fun req => do
    if hasMethod req .get ∧ hasUri req "/api/users"
    then return Response.ok "users list"
    else return Response.notFound

  expected := "HTTP/1.1 200 OK\x0d\nContent-Length: 10\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nusers list"
}

#eval runTestCase {
  name := "POST with body"
  request := Request.new
    |>.method .post
    |>.uri! "/api/users"
    |>.header! "Host" "api.example.com"
    |>.header! "Content-Type" "application/json"
    |>.header! "Content-Length" "20"
    |>.body #[.mk "{\"name\":\"Alice\"}".toUTF8 #[]]

  handler := fun req => do
    if hasMethod req .post ∧ hasHeader req "Content-Type" "application/json"
    then return Response.new |>.status .created |>.body "Created"
    else return Response.badRequest
  expected := "HTTP/1.1 201 Created\x0d\nContent-Length: 7\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nCreated"
}

#eval runTestCase {
  name := "DELETE request"

  request := Request.new
    |>.method .delete
    |>.uri! "/api/users/123"
    |>.header! "Host" "api.example.com"
    |>.body #[]

  handler := fun req => do
    if hasMethod req .delete ∧ hasUri req "/api/users/123"
    then return Response.new |>.status .noContent |>.body ""
    else return Response.notFound

  expected := "HTTP/1.1 204 No Content\x0d\nContent-Length: 0\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
}

#eval runTestCase {
  name := "HEAD request"

  request := Request.new
    |>.method .head
    |>.uri! "/api/users"
    |>.header! "Host" "api.example.com"
    |>.body #[]

  handler := fun req => do
    if hasMethod req .head
    then return Response.ok ""
    else return Response.notFound

  expected := "HTTP/1.1 200 OK\x0d\nContent-Length: 0\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
}

#eval runTestCase {
  name := "OPTIONS request"

  request := Request.new
    |>.method .options
    |>.uri! "*"
    |>.header! "Host" "api.example.com"
    |>.body #[]

  handler := fun req => do
    if hasMethod req .options
    then return Response.new
      |>.status .ok
      |>.header! "Allow" "GET, POST, PUT, DELETE, OPTIONS"
      |>.body ""
    else return Response.badRequest

  expected := "HTTP/1.1 200 OK\x0d\nAllow: GET, POST, PUT, DELETE, OPTIONS\x0d\nContent-Length: 0\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
}

#eval runTestCase {
  name := "Request with multiple headers"

  request := Request.new
    |>.method .get
    |>.uri! "/api/data"
    |>.header! "Host" "api.example.com"
    |>.header! "Accept" "application/json"
    |>.header! "User-Agent" "TestClient/1.0"
    |>.header! "Authorization" "Bearer token123"
    |>.body #[]

  handler := fun req => do
    if hasHeader req "Authorization" "Bearer token123" ∧ hasHeader req "Accept" "application/json"
    then return Response.ok "authenticated"
    else return Response.new |>.status .unauthorized |>.body "unauthorized"

  expected := "HTTP/1.1 200 OK\x0d\nContent-Length: 13\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nauthenticated"
}

#eval runTestCase {
  name := "Request with query parameters"

  request := Request.new
    |>.method .get
    |>.uri! "/api/search?q=test&limit=10"
    |>.header! "Host" "api.example.com"
    |>.body #[]

  handler := fun req => do
    if hasUri req "/api/search?q=test&limit=10"
    then return Response.ok "search results"
    else return Response.notFound

  expected := "HTTP/1.1 200 OK\x0d\nContent-Length: 14\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nsearch results"
}

#eval runTestCase {
  name := "POST with empty body"

  request := Request.new
    |>.method .post
    |>.uri! "/api/trigger"
    |>.header! "Host" "api.example.com"
    |>.header! "Content-Length" "0"
    |>.body #[]

  handler := fun req => do
    if hasMethod req .post ∧ hasContentLength req "0"
    then return Response.new |>.status .accepted |>.body "triggered"
    else return Response.badRequest

  expected := "HTTP/1.1 202 Accepted\x0d\nContent-Length: 9\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\ntriggered"
}

#eval runTestCase {
  name := "Large response body"

  request := Request.new
    |>.method .get
    |>.uri! "/api/large"
    |>.header! "Host" "api.example.com"
    |>.body #[]

  handler := fun _ => do
    let largeBody := String.mk (List.replicate 1000 'X')
    return Response.ok largeBody

  expected := s!"HTTP/1.1 200 OK\x0d\nContent-Length: 1000\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n{String.mk (List.replicate 1000 'X')}"
}

#eval runTestCase {
  name := "Custom status code"

  request := Request.new
    |>.method .get
    |>.uri! "/api/teapot"
    |>.header! "Host" "api.example.com"
    |>.body #[]

  handler := fun _ => do
    return Response.new
      |>.status .imATeapot
      |>.body "I'm a teapot"

  expected := "HTTP/1.1 418 I'm a teapot\x0d\nContent-Length: 12\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nI'm a teapot"
}

#eval runTestCase {
  name := "Request with special characters in URI"
  request := Request.new
    |>.method .get
    |>.uri! "/api/users/%C3%A9"
    |>.header! "Host" "api.example.com"
    |>.body #[]
  handler := fun req => do
    if hasUri req "/api/users/%C3%A9"
    then return Response.ok "found"
    else return Response.notFound
  expected := "HTTP/1.1 200 OK\x0d\nContent-Length: 5\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nfound"
}

#eval runTestCase {
  name := "Response with custom headers"

  request := Request.new
    |>.method .get
    |>.uri! "/api/data"
    |>.header! "Host" "api.example.com"
      |>.header! "Cache-Control" "no-cache"
    |>.body #[]

  handler := fun _ => do
    return Response.new
      |>.status .ok
      |>.header! "Cache-Control" "no-cache"
      |>.header! "X-Custom-Header" "custom-value"
      |>.body "data"

  expected := "HTTP/1.1 200 OK\x0d\nX-Custom-Header: custom-value\x0d\nContent-Length: 4\x0d\nServer: LeanHTTP/1.1\x0d\nCache-Control: no-cache\x0d\n\x0d\ndata"
}

#eval runTestCase {
  name := "Request with Content-Type and body"

  request := Request.new
    |>.method .post
    |>.uri! "/api/xml"
    |>.header! "Host" "api.example.com"
    |>.header! "Content-Type" "application/xml"
    |>.header! "Content-Length" "17"
    |>.body #[.mk "<data>test</data>".toUTF8 #[]]

  handler := fun req => do
    if hasHeader req "Content-Type" "application/xml"
    then return Response.ok "processed xml"
    else return Response.new |>.status .unsupportedMediaType |>.body "unsupported"

  expected := "HTTP/1.1 200 OK\x0d\nContent-Length: 13\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nprocessed xml"
}

#eval runTestCase {
  name := "Request with Content-Type and body"

  request := Request.new
    |>.method .post
    |>.uri! "/api/xml"
    |>.header! "Host" "api.example.com"
    |>.header! "Content-Type" "application/xml"
    |>.header! "Content-Length" "17"
    |>.body #[.mk "<data>test</data>".toUTF8 #[]]

  handler := fun req => do
    if hasHeader req "Content-Type" "application/xml"
    then return Response.ok "processed xml"
    else return Response.new |>.status .unsupportedMediaType |>.body "unsupported"

  expected := "HTTP/1.1 200 OK\x0d\nContent-Length: 13\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nprocessed xml"
}

#eval runTestCase {
  name := "Streaming response with fixed Content-Length"

  request := Request.new
    |>.method .get
    |>.uri! "/stream"
    |>.header! "Host" "example.com"
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

  expected := "HTTP/1.1 200 OK\x0d\nContent-Length: 21\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nchunk0\nchunk1\nchunk2\n"
}

#eval runTestCase {
  name := "Streaming response with setKnownSize fixed"

  request := Request.new
    |>.method .get
    |>.uri! "/stream-sized"
    |>.header! "Host" "example.com"
    |>.body #[]

  handler := fun req => do
    let stream ← Body.ByteStream.empty
    stream.setKnownSize (some (.fixed 15))

    background do
      for i in [0:3] do
        discard <| stream.write s!"data{i}".toUTF8

      stream.close

    return Response.ok stream .empty

  expected := "HTTP/1.1 200 OK\x0d\nContent-Length: 15\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\ndata0data1data2"
}

#eval runTestCase {
  name := "Streaming response with chunked encoding"

  request := Request.new
    |>.method .get
    |>.uri! "/stream-chunked"
    |>.header! "Host" "example.com"
    |>.body #[]

  handler := fun req => do
    let stream ← Body.ByteStream.empty

    background do
      discard <| stream.write "hello".toUTF8
      discard <| stream.write "world".toUTF8
      stream.close
    return Response.ok stream .empty

  expected := "HTTP/1.1 200 OK\x0d\nTransfer-Encoding: chunked\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n5\x0d\nhello\x0d\n5\x0d\nworld\x0d\n0\x0d\n\x0d\n"
}

#eval runTestCase {
  name := "Chunked request with streaming response"

  request := Request.new
    |>.method .post
    |>.uri! "/"
    |>.header! "Host" "example.com"
    |>.header! "Transfer-Encoding" "chunked"
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
      return Response.ok stream (.empty |>.insert "Content-Length" "18")
    else
      return Response.badRequest "not chunked"

  expected := "HTTP/1.1 200 OK\x0d\nContent-Length: 18\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nresponse0response1"
  chunked := true
}

#eval runTestCase {
  name := "Chunked request with streaming response"

  request := Request.new
    |>.method .post
    |>.uri! "/"
    |>.header! "Host" "example.com"
    |>.header! "Transfer-Encoding" "chunked"
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
      return Response.ok stream (.empty |>.insert "Content-Length" "18")
    else
      return Response.badRequest "not chunked"

  expected := "HTTP/1.1 200 OK\x0d\nContent-Length: 18\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nresponse0response1"
  chunked := true
}


-- Limits

#eval
  let bigString := String.fromUTF8! (ByteArray.mk (Array.ofFn (n := 257) (fun _ => 65)))

  runTestCase {
  name := "Huge String request"

  request := Request.new
    |>.method .head
    |>.uri! "/api/users"
    |>.header! "Host" "api.example.com"
    |>.header! bigString "a"
    |>.body #[]

  handler := fun req => do
    if hasMethod req .head
    then return Response.ok "" (Headers.empty |>.insert bigString "ata")
    else return Response.notFound
  expected := "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
}

#eval runTestCase {
  name := "Request line too long"

  request :=
    Request.new
    |>.method .get
    |>.uri (.originForm (.mk #[String.mk (List.replicate 2000 'a')] true) none none)
    |>.header! "Host" "api.example.com"
    |>.body #[]

  handler := fun req => do
    return Response.ok (toString (toString req.head.uri).length)

  expected := "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
}


#eval runTestCase {
  name := "Header long"

  request :=
    Request.new
    |>.method .get
    |>.uri (.originForm (.mk #[String.mk (List.replicate 200 'a')] true) none none)
    |>.header! "Host" (.ofString! (String.mk (List.replicate 8230 'a')))
    |>.body #[]

  handler := fun req => do
    return Response.ok (toString (toString req.head.uri).length)

  expected := "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
}

#eval runTestCase {
  name := "Too many headers"

  request := Id.run do
    let mut req := Request.new
      |>.method .get
      |>.uri! "/api/data"
      |>.header! "Host" "api.example.com"

    for i in [0:101] do
      req := req |>.header! s!"X-Header-{i}" (.ofString! s!"value{i}")

    return req |>.body #[]

  handler := fun _ => do
    return Response.ok "success"

  expected := "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
}

#eval runTestCase {
  name := "Header value too long"

  request := Request.new
    |>.method .get
    |>.uri! "/api/test"
    |>.header! "Host" "api.example.com"
    |>.header! "X-Long-Value" (.ofString! (String.mk (List.replicate 9000 'x')))
    |>.body #[]

  handler := fun _ => do
    return Response.ok "ok"

  expected := "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
}

#eval runTestCase {
  name := "Total headers size too large"

  request := Id.run do
    let mut req := Request.new
      |>.method .get
      |>.uri! "/api/data"
      |>.header! "Host" "api.example.com"

    for i in [0:200] do
      req := req |>.header! s!"X-Header-{i}" (.ofString! (String.mk (List.replicate 200 'a')))
    return req |>.body #[]

  handler := fun _ => do
    return Response.ok "success"

  expected := "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
}
