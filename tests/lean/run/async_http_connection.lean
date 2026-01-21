import Std.Internal.Http
import Std.Internal.Async
import Std.Internal.Async.Timer

open Std.Internal.IO Async
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
    |>.run

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
       Expected:\n{expected.quote}\n\
       Got:\n{responseData.quote}"

def runTestCase (tc : TestCase) : IO Unit := do
  let (client, server) ← Mock.new
  runTest tc.name client server tc.request tc.handler tc.expected tc.chunked

-- Request Predicates

/-- Check if request is a basic GET requests to the specified URI and host. -/
def isBasicGetRequest (req : Request Body) (uri : String) (host : String) : Bool :=
  req.head.method == .get ∧
  req.head.version == .v11 ∧
  toString req.head.uri = uri ∧
  req.head.headers.hasEntry (.new "host") (.ofString! host)

/-- Check if request has a specific Content-Length header. -/
def hasContentLength (req : Request Body) (length : String) : Bool :=
  req.head.headers.hasEntry (.new "content-length")  (.ofString! length)

/-- Check if request uses chunked transfer encoding. -/
def isChunkedRequest (req : Request Body) : Bool :=
  req.head.headers.hasEntry (.new "transfer-encoding") (.ofString! "chunked")

/-- Check if request has a specific header with a specific value. -/
def hasHeader (req : Request Body) (name : String) (value : String) : Bool :=
  if let some name := Header.Name.ofString? name then
    req.head.headers.hasEntry name (.ofString! value)
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
    |>.header! "Connection" "close"
    |>.header! "Content-Length" "7"
    |>.body #[.mk "survive".toUTF8 #[]]

  handler := fun req => do
    if isBasicGetRequest req "/" "example.com" ∧ hasContentLength req "7"
    then return Response.ok |>.body "ok"
    else return Response.badRequest |>.body "invalid"

  expected := "HTTP/1.1 200 OK\x0d\nContent-Length: 2\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nok"
}

#eval runTestCase {
  name := "Simple GET request"

  request := Request.new
    |>.method .get
    |>.uri! "/api/users"
    |>.header! "Host" "api.example.com"
    |>.header! "Connection" "close"
    |>.body #[]

  handler := fun req => do
    if hasMethod req .get ∧ hasUri req "/api/users"
    then return Response.ok |>.body "users list"
    else return Response.notFound |>.body ()

  expected := "HTTP/1.1 200 OK\x0d\nContent-Length: 10\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nusers list"
}

#eval runTestCase {
  name := "POST with body"
  request := Request.new
    |>.method .post
    |>.uri! "/api/users"
    |>.header! "Host" "api.example.com"
    |>.header! "Content-Type" "application/json"
    |>.header! "Content-Length" "16"
    |>.header! "Connection" "close"
    |>.body #[.mk "{\"name\":\"Alice\"}".toUTF8 #[]]

  handler := fun req => do
    if hasMethod req .post ∧ hasHeader req "Content-Type" "application/json"
    then return Response.new |>.status .created |>.body "Created"
    else return Response.badRequest |>.body ()
  expected := "HTTP/1.1 201 Created\x0d\nContent-Length: 7\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nCreated"
}

#eval runTestCase {
  name := "DELETE request"

  request := Request.new
    |>.method .delete
    |>.uri! "/api/users/123"
    |>.header! "Host" "api.example.com"
    |>.header! "Connection" "close"
    |>.body #[]

  handler := fun req => do
    if hasMethod req .delete ∧ hasUri req "/api/users/123"
    then return Response.new |>.status .noContent |>.body ""
    else return Response.notFound |>.body ()

  expected := "HTTP/1.1 204 No Content\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
}

#eval runTestCase {
  name := "HEAD request"

  request := Request.new
    |>.method .head
    |>.uri! "/api/users"
    |>.header! "Host" "api.example.com"
    |>.header! "Connection" "close"
    |>.body #[]

  handler := fun req => do
    if hasMethod req .head
    then return Response.ok |>.body ""
    else return Response.notFound |>.body ()

  expected := "HTTP/1.1 200 OK\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
}

#eval runTestCase {
  name := "OPTIONS request"

  request := Request.new
    |>.method .options
    |>.uri! "*"
    |>.header! "Host" "api.example.com"
    |>.header! "Connection" "close"
    |>.body #[]

  handler := fun req => do
    if hasMethod req .options
    then return Response.new
      |>.status .ok
      |>.header! "Allow" "GET, POST, PUT, DELETE, OPTIONS"
      |>.body ""
    else return Response.badRequest |>.body ()

  expected := "HTTP/1.1 200 OK\x0d\nAllow: GET, POST, PUT, DELETE, OPTIONS\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
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
    |>.header! "Connection" "close"
    |>.body #[]

  handler := fun req => do
    if hasHeader req "Authorization" "Bearer token123" ∧ hasHeader req "Accept" "application/json"
    then return Response.ok |>.body "authenticated"
    else return Response.new |>.status .unauthorized |>.body "unauthorized"

  expected := "HTTP/1.1 200 OK\x0d\nContent-Length: 13\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nauthenticated"
}

#eval runTestCase {
  name := "Request with query parameters"

  request := Request.new
    |>.method .get
    |>.uri! "/api/search?q=test&limit=10"
    |>.header! "Host" "api.example.com"
    |>.header! "Connection" "close"
    |>.body #[]

  handler := fun req => do
    if hasUri req "/api/search?q=test&limit=10"
    then return Response.ok |>.body "search results"
    else return Response.notFound |>.body ()

  expected := "HTTP/1.1 200 OK\x0d\nContent-Length: 14\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nsearch results"
}

#eval runTestCase {
  name := "POST with empty body"

  request := Request.new
    |>.method .post
    |>.uri! "/api/trigger"
    |>.header! "Host" "api.example.com"
    |>.header! "Content-Length" "0"
    |>.header! "Connection" "close"
    |>.body #[]

  handler := fun req => do
    if hasMethod req .post ∧ hasContentLength req "0"
    then return Response.new |>.status .accepted |>.body "triggered"
    else return Response.badRequest |>.body ()

  expected := "HTTP/1.1 202 Accepted\x0d\nContent-Length: 9\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\ntriggered"
}

#eval runTestCase {
  name := "Large response body"

  request := Request.new
    |>.method .get
    |>.uri! "/api/large"
    |>.header! "Host" "api.example.com"
    |>.header! "Connection" "close"
    |>.body #[]

  handler := fun _ => do
    let largeBody := String.ofList (List.replicate 1000 'X')
    return Response.ok |>.body largeBody

  expected := s!"HTTP/1.1 200 OK\x0d\nContent-Length: 1000\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n{String.ofList (List.replicate 1000 'X')}"
}

#eval runTestCase {
  name := "Custom status code"

  request := Request.new
    |>.method .get
    |>.uri! "/api/teapot"
    |>.header! "Host" "api.example.com"
    |>.header! "Connection" "close"
    |>.body #[]

  handler := fun _ => do
    return Response.new
      |>.status .imATeapot
      |>.body "I'm a teapot"

  expected := "HTTP/1.1 418 I'm a teapot\x0d\nContent-Length: 12\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nI'm a teapot"
}

#eval runTestCase {
  name := "Request with special characters in URI"
  request := Request.new
    |>.method .get
    |>.uri! "/api/users/%C3%A9"
    |>.header! "Host" "api.example.com"
    |>.header! "Connection" "close"
    |>.body #[]
  handler := fun req => do
    if hasUri req "/api/users/%C3%A9"
    then return Response.ok |>.body "found"
    else return Response.notFound |>.body ()
  expected := "HTTP/1.1 200 OK\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nfound"
}

#eval runTestCase {
  name := "Response with custom headers"

  request := Request.new
    |>.method .get
    |>.uri! "/api/data"
    |>.header! "Host" "api.example.com"
    |>.header! "Connection" "close"
    |>.header! "Cache-Control" "no-cache"
    |>.body #[]

  handler := fun _ => do
    return Response.new
      |>.status .ok
      |>.header! "Cache-Control" "no-cache"
      |>.header! "X-Custom-Header" "custom-value"
      |>.body "data"

  expected := "HTTP/1.1 200 OK\x0d\nX-Custom-Header: custom-value\x0d\nContent-Length: 4\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\nCache-Control: no-cache\x0d\n\x0d\ndata"
}

#eval runTestCase {
  name := "Request with Content-Type and body"

  request := Request.new
    |>.method .post
    |>.uri! "/api/xml"
    |>.header! "Host" "api.example.com"
    |>.header! "Content-Type" "application/xml"
    |>.header! "Content-Length" "17"
    |>.header! "Connection" "close"
    |>.body #[.mk "<data>test</data>".toUTF8 #[]]

  handler := fun req => do
    if hasHeader req "Content-Type" "application/xml"
    then return Response.ok |>.body "processed xml"
    else return Response.new |>.status .unsupportedMediaType |>.body "unsupported"

  expected := "HTTP/1.1 200 OK\x0d\nContent-Length: 13\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nprocessed xml"
}

#eval runTestCase {
  name := "Request with Content-Type and body"

  request := Request.new
    |>.method .post
    |>.uri! "/api/xml"
    |>.header! "Host" "api.example.com"
    |>.header! "Content-Type" "application/xml"
    |>.header! "Content-Length" "17"
    |>.header! "Connection" "close"
    |>.body #[.mk "<data>test</data>".toUTF8 #[]]

  handler := fun req => do
    if hasHeader req "Content-Type" "application/xml"
    then return Response.ok |>.body "processed xml"
    else return Response.new |>.status .unsupportedMediaType |>.body "unsupported"

  expected := "HTTP/1.1 200 OK\x0d\nContent-Length: 13\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nprocessed xml"
}
