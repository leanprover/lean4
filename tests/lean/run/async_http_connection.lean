import Std.Internal.Http
import Std.Internal.Async
import Std.Internal.Async.Timer

open Std.Internal.IO Async
open Std Http

abbrev TestHandler := Request Body.Incoming → ContextAsync (Response Body.Outgoing)

instance : Std.Http.Server.Handler TestHandler where
  onRequest handler request := handler request

instance : Coe (ContextAsync (Response Body.Incoming)) (ContextAsync (Response Body.Outgoing)) where
  coe action := do
    let response ← action
    pure { response with body := response.body.toOutgoing }

instance : Coe (Async (Response Body.Incoming)) (ContextAsync (Response Body.Outgoing)) where
  coe action := do
    let response ← action
    pure { response with body := response.body.toOutgoing }


structure TestCase where
  /-- Descriptive name for the test -/
  name : String
  /-- The HTTP request to send -/
  request : Request (Array Chunk)
  /-- Handler function to process the request -/
  handler : Request Body.Incoming → ContextAsync (Response Body.Outgoing)
  /-- Expected response string -/
  expected : String
  /-- Whether to use chunked encoding -/
  chunked : Bool := false
  deriving Inhabited

def toByteArray (req : Request (Array Chunk)) (chunked := false) : IO ByteArray := Async.block do
  let mut data := Internal.Encode.encode (v := .v11) .empty req.head
  let toByteArray (chunkData : Internal.ChunkedBuffer) (part : Chunk) := Internal.Encode.encode .v11 chunkData part

  for part in req.body do data := toByteArray data part

  if chunked then data := toByteArray data (Chunk.mk .empty .empty)

  return data.toByteArray

/-- Send multiple requests through a mock connection and return the response data. -/
def sendRequests (client : Mock.Client) (server : Mock.Server) (reqs : Array (Request (Array Chunk)))
    (onRequest : Request Body.Incoming → ContextAsync (Response Body.Outgoing))
    (chunked : Bool := false) : IO ByteArray := Async.block do
  let mut data := .empty
  for req in reqs do data := data ++ (← toByteArray req chunked)

  client.send data
  Std.Http.Server.serveConnection server onRequest { lingeringTimeout := 3000, generateDate := false }
    |>.run

  let res ← client.recv?
  pure <| res.getD .empty

/-- Run a single test case, comparing actual response against expected response. -/
def runTest (name : String) (client : Mock.Client) (server : Mock.Server) (req : Request (Array Chunk))
    (handler : Request Body.Incoming → ContextAsync (Response Body.Outgoing)) (expected : String) (chunked : Bool := false) :
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
  Async.block <| runTest tc.name client server tc.request tc.handler tc.expected tc.chunked

-- Request Predicates

/-- Check if request is a basic GET requests to the specified URI and host. -/
def isBasicGetRequest (req : Request Body.Incoming) (uri : String) (host : String) : Bool :=
  req.head.method == .get ∧
  req.head.version == .v11 ∧
  toString req.head.uri = uri ∧
  req.head.headers.hasEntry (.mk "host") (.ofString! host)

/-- Check if request has a specific Content-Length header. -/
def hasContentLength (req : Request Body.Incoming) (length : String) : Bool :=
  req.head.headers.hasEntry (.mk "content-length")  (.ofString! length)

/-- Check if request uses chunked transfer encoding. -/
def isChunkedRequest (req : Request Body.Incoming) : Bool :=
  if let some te := req.head.headers.get? (.mk "transfer-encoding") then
    match Header.TransferEncoding.parse te with
    | some te => te.isChunked
    | none => false
  else
    false

/-- Check if request has a specific header with a specific value. -/
def hasHeader (req : Request Body.Incoming) (name : String) (value : String) : Bool :=
  if let some name := Header.Name.ofString? name then
    req.head.headers.hasEntry name (.ofString! value)
  else
    false

/-- Check if request method matches the expected method. -/
def hasMethod (req : Request Body.Incoming) (method : Method) : Bool :=
  req.head.method == method

/-- Check if request URI matches the expected URI string. -/
def hasUri (req : Request Body.Incoming) (uri : String) : Bool :=
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
    then Response.ok |>.text "ok"
    else Response.badRequest |>.text "closed"

  expected := "HTTP/1.1 200 OK\x0d\nContent-Length: 2\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\nContent-Type: text/plain; charset=utf-8\x0d\n\x0d\nok"
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
    then Response.ok |>.text "users list"
    else Response.notFound |>.text ""

  expected := "HTTP/1.1 200 OK\x0d\nContent-Length: 10\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\nContent-Type: text/plain; charset=utf-8\x0d\n\x0d\nusers list"
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
    then Response.new |>.status .created |>.text "Created"
    else Response.badRequest |>.text ""
  expected := "HTTP/1.1 201 Created\x0d\nContent-Length: 7\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\nContent-Type: text/plain; charset=utf-8\x0d\n\x0d\nCreated"
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
    then Response.new |>.status .noContent |>.text ""
    else Response.notFound |>.text ""

  expected := "HTTP/1.1 204 No Content\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\nContent-Type: text/plain; charset=utf-8\x0d\n\x0d\n"
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
    then Response.ok |>.text ""
    else Response.notFound |>.text ""

  expected := "HTTP/1.1 200 OK\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\nContent-Type: text/plain; charset=utf-8\x0d\n\x0d\n"
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
    then Response.new
      |>.status .ok
      |>.header! "Allow" "GET, POST, PUT, DELETE, OPTIONS"
      |>.text ""
    else Response.badRequest |>.text ""

  expected := "HTTP/1.1 200 OK\x0d\nAllow: GET, POST, PUT, DELETE, OPTIONS\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\nContent-Type: text/plain; charset=utf-8\x0d\n\x0d\n"
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
    then Response.ok |>.text "authenticated"
    else Response.new |>.status .unauthorized |>.text "unauthorized"

  expected := "HTTP/1.1 200 OK\x0d\nContent-Length: 13\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\nContent-Type: text/plain; charset=utf-8\x0d\n\x0d\nauthenticated"
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
    then Response.ok |>.text "search results"
    else Response.notFound |>.text ""

  expected := "HTTP/1.1 200 OK\x0d\nContent-Length: 14\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\nContent-Type: text/plain; charset=utf-8\x0d\n\x0d\nsearch results"
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
    then Response.new |>.status .accepted |>.text "triggered"
    else Response.badRequest |>.text ""

  expected := "HTTP/1.1 202 Accepted\x0d\nContent-Length: 9\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\nContent-Type: text/plain; charset=utf-8\x0d\n\x0d\ntriggered"
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
    Response.ok |>.text largeBody

  expected := s!"HTTP/1.1 200 OK\x0d\nContent-Length: 1000\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\nContent-Type: text/plain; charset=utf-8\x0d\n\x0d\n{String.ofList (List.replicate 1000 'X')}"
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
    Response.new
      |>.status .imATeapot
      |>.text "I'm a teapot"

  expected := "HTTP/1.1 418 I'm a teapot\x0d\nContent-Length: 12\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\nContent-Type: text/plain; charset=utf-8\x0d\n\x0d\nI'm a teapot"
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
    then Response.ok |>.text "found"
    else Response.notFound |>.text ""
  expected := "HTTP/1.1 200 OK\x0d\nContent-Length: 5\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\nContent-Type: text/plain; charset=utf-8\x0d\n\x0d\nfound"
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
    Response.new
      |>.status .ok
      |>.header! "Cache-Control" "no-cache"
      |>.header! "X-Custom-Header" "custom-value"
      |>.text "data"

  expected := "HTTP/1.1 200 OK\x0d\nX-Custom-Header: custom-value\x0d\nContent-Length: 4\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\nContent-Type: text/plain; charset=utf-8\x0d\nCache-Control: no-cache\x0d\n\x0d\ndata"
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
    then Response.ok |>.text "processed xml"
    else Response.new |>.status .unsupportedMediaType |>.text "unsupported"

  expected := "HTTP/1.1 200 OK\x0d\nContent-Length: 13\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\nContent-Type: text/plain; charset=utf-8\x0d\n\x0d\nprocessed xml"
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
    |>.header! "Connection" "close"
    |>.body #[]

  handler := fun req => do
    if hasMethod req .head
    then Response.ok
      |>.header (.ofString! bigString) (.ofString! "ata")
      |>.text ""
    else Response.notFound |>.text ""
  expected := "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
}

#eval runTestCase {
  name := "Request line too long"

  request :=
    Request.new
    |>.method .get
    |>.uri (.originForm (.mk #[URI.EncodedString.encode <| String.ofList (List.replicate 2000 'a')] true) none)
    |>.header! "Host" "api.example.com"
    |>.header! "Connection" "close"
    |>.body #[]

  handler := fun req => do
    Response.ok |>.text (toString (toString req.head.uri).length)

  expected := "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
}

#eval runTestCase {
  name := "Header long"

  request :=
    Request.new
    |>.method .get
    |>.uri (.originForm (.mk #[URI.EncodedString.encode <| String.ofList (List.replicate 200 'a')] true) none)
    |>.header! "Host" (String.ofList (List.replicate 8230 'a'))
    |>.header! "Connection" "close"
    |>.body #[]

  handler := fun req => do
    Response.ok |>.text (toString (toString req.head.uri).length)

  expected := "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
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
    Response.ok |>.text "success"

  expected := "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
}

#eval runTestCase {
  name := "Header value too long"

  request := Request.new
    |>.method .get
    |>.uri! "/api/test"
    |>.header! "Host" "api.example.com"
    |>.header! "X-Long-Value" (String.ofList (List.replicate 9000 'x'))
    |>.header! "Connection" "close"
    |>.body #[]

  handler := fun _ => do
    Response.ok |>.text "ok"

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
      req := req |>.header! s!"X-Header-{i}" (String.ofList (List.replicate 200 'a'))
    return req |>.body #[]

  handler := fun _ => do
    Response.ok |>.text "success"

  expected := "HTTP/1.1 400 Bad Request\x0d\nContent-Length: 0\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
}

-- Tests

#eval runTestCase {
  name := "Streaming response with fixed Content-Length"

  request := Request.new
    |>.method .get
    |>.uri! "/stream"
    |>.header! "Host" "example.com"
    |>.header! "Connection" "close"
    |>.body #[]

  handler := fun _ => do
    let (stream, _incoming) ← Body.mkChannel

    background do
      for i in [0:3] do
        let sleep ← Sleep.mk 5
        sleep.wait
        stream.send <| Chunk.ofByteArray s!"chunk{i}\n".toUTF8
      stream.close

    return Response.ok
      |>.header (.mk "content-length") (.mk "21")
      |>.body stream

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
    let (stream, _incoming) ← Body.mkChannel
    stream.setKnownSize (some (.fixed 15))

    background do
      for i in [0:3] do
        stream.send <| Chunk.ofByteArray s!"data{i}".toUTF8

      stream.close

    return Response.ok
      |>.body stream

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
    let (stream, _incoming) ← Body.mkChannel

    background do
      stream.send <| Chunk.ofByteArray "hello".toUTF8
      stream.send <| Chunk.ofByteArray "world".toUTF8
      stream.close
    return Response.ok
      |>.body stream

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
    let (stream, _incoming) ← Body.mkChannel

    if isChunkedRequest req
    then
      background do
        for i in [0:2] do
          stream.send <| Chunk.ofByteArray s!"response{i}".toUTF8
        stream.close
      return Response.ok
        |>.header (.mk "content-length") (.mk "18")
        |>.body stream
    else
      stream.send <| Chunk.ofByteArray "not chunked".toUTF8
      stream.close

      return Response.badRequest
        |>.body stream

  expected := "HTTP/1.1 200 OK\x0d\nContent-Length: 18\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nresponse0response1"
  chunked := true
}

#eval runTestCase {
  name := "Chunked request with streaming response and other encodings"

  request := Request.new
    |>.method .post
    |>.uri! "/"
    |>.header! "Host" "example.com"
    |>.header! "Transfer-Encoding" "gzip, chunked"
    |>.header! "Connection" "close"
    |>.body #[
      .mk "data1".toUTF8 #[],
      .mk "data2".toUTF8 #[]
    ]

  handler := fun req => do
    let (stream, _incoming) ← Body.mkChannel

    if isChunkedRequest req
    then
      background do
        for i in [0:2] do
          stream.send <| Chunk.ofByteArray s!"response{i}".toUTF8
        stream.close
      return Response.ok
        |>.header (.mk "content-length") (.mk "18")
        |>.body stream
    else
      stream.send <| Chunk.ofByteArray "not chunked".toUTF8
      stream.close

      return Response.badRequest
        |>.body stream

  expected := "HTTP/1.1 200 OK\x0d\nContent-Length: 18\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nresponse0response1"
  chunked := true
}
