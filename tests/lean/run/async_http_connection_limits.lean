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
    |>.header! "Connection" "close"
    |>.body #[]

  handler := fun req => do
    if hasMethod req .head
    then return Response.ok "" (Headers.empty |>.insert (.ofString! bigString) (.ofString! "ata"))
    else return Response.notFound
  expected := "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
}

#eval runTestCase {
  name := "Request line too long"

  request :=
    Request.new
    |>.method .get
    |>.uri (.originForm (.mk #[String.mk (List.replicate 2000 'a')] true) none none)
    |>.header! "Host" "api.example.com"
    |>.header! "Connection" "close"
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
    |>.header! "Host" (String.mk (List.replicate 8230 'a'))
    |>.header! "Connection" "close"
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
      |>.header! "Connection" "close"

    for i in [0:101] do
      req := req |>.header! s!"X-Header-{i}" s!"value{i}"

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
    |>.header! "X-Long-Value" (String.mk (List.replicate 9000 'x'))
      |>.header! "Connection" "close"
    |>.body #[]

  handler := fun _ => do
    return Response.ok "ok"

  expected := "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
}

#eval runTestCase {
  name := "Total headers size too large"

  request := Id.run do
    let mut req := Request.new
      |>.method .get
      |>.uri! "/api/data"
      |>.header! "Host" "api.example.com"
      |>.header! "Connection" "close"

    for i in [0:200] do
      req := req |>.header! s!"X-Header-{i}" (String.mk (List.replicate 200 'a'))
    return req |>.body #[]

  handler := fun _ => do
    return Response.ok "success"

  expected := "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
}
