import Std.Internal.Http
import Std.Internal.Async

open Std.Internal.IO Async
open Std Http

abbrev TestHandler := Request Body.Stream → ContextAsync (Response Body.Stream)

instance : Std.Http.Server.Handler TestHandler where
  onRequest handler request := handler request


/-- Send raw bytes to the server and return the response. -/
def sendRaw (client : Mock.Client) (server : Mock.Server) (raw : ByteArray)
    (handler : Request Body.Stream → ContextAsync (Response Body.Stream))
    (config : Config := { lingeringTimeout := 3000 }) : IO ByteArray := Async.block do
  client.send raw
  Std.Http.Server.serveConnection server handler config
    |>.run
  let res ← client.recv?
  pure <| res.getD .empty

structure TestCase where
  name : String
  request : Request (Array Chunk)
  handler : Request Body.Stream → ContextAsync (Response Body.Stream)
  config : Config := { lingeringTimeout := 3000 }
  check : String → IO Unit
  chunked : Bool := false

def toByteArray (req : Request (Array Chunk)) (chunked := false) : IO ByteArray := Async.block do
  let mut data := Internal.Encode.encode (v := .v11) .empty req.head
  let toByteArray (chunkData : Internal.ChunkedBuffer) (part : Chunk) := Internal.Encode.encode .v11 chunkData part
  for part in req.body do data := toByteArray data part
  if chunked then data := toByteArray data (Chunk.mk .empty .empty)
  return data.toByteArray

def runTestCase (tc : TestCase) : IO Unit := do
  let (client, server) ← Mock.new
  let raw ← toByteArray tc.request tc.chunked
  let response ← sendRaw client server raw tc.handler tc.config
  let responseData := String.fromUTF8! response
  tc.check responseData

-- Test: Date header is automatically generated when generateDate is true
#eval runTestCase {
  name := "Date header auto-generated"

  request := Request.new
    |>.method .get
    |>.uri! "/"
    |>.header! "Host" "example.com"
    |>.header! "Connection" "close"
    |>.body #[]

  config := { lingeringTimeout := 3000, generateDate := true }

  handler := fun _ => do
    Response.ok |>.text "hello"

  check := fun response => do
    unless response.contains "Date: " do
      throw <| IO.userError s!"Expected Date header in response but got:\n{response}"
    unless response.contains "200 OK" do
      throw <| IO.userError s!"Expected 200 OK in response but got:\n{response}"
}

-- Test: Date header is NOT generated when generateDate is false
#eval runTestCase {
  name := "Date header not generated when disabled"

  request := Request.new
    |>.method .get
    |>.uri! "/"
    |>.header! "Host" "example.com"
    |>.header! "Connection" "close"
    |>.body #[]

  config := { lingeringTimeout := 3000, generateDate := false }

  handler := fun _ => do
    Response.ok |>.text "hello"

  check := fun response => do
    if response.contains "Date: " then
      throw <| IO.userError s!"Date header should NOT be present when generateDate is false:\n{response}"
}

-- Test: User-set Date header is not overwritten
#eval runTestCase {
  name := "User-set Date header preserved"

  request := Request.new
    |>.method .get
    |>.uri! "/"
    |>.header! "Host" "example.com"
    |>.header! "Connection" "close"
    |>.body #[]

  config := { lingeringTimeout := 3000, generateDate := true }

  handler := fun _ => do
    Response.ok
      |>.header! "Date" "Mon, 01 Jan 2024 00:00:00 GMT"
      |>.text "hello"

  check := fun response => do
    unless response.contains "Date: Mon, 01 Jan 2024 00:00:00 GMT" do
      throw <| IO.userError s!"User-set Date header should be preserved:\n{response}"
}

-- Test: Normal POST without Expect does NOT get 100 Continue
#eval runTestCase {
  name := "No 100-continue without Expect header"

  request := Request.new
    |>.method .post
    |>.uri! "/upload"
    |>.header! "Host" "example.com"
    |>.header! "Content-Length" "5"
    |>.header! "Connection" "close"
    |>.body #[.mk "hello".toUTF8 #[]]

  config := { lingeringTimeout := 3000, generateDate := false }

  handler := fun req => do
    let body : String ← req.body.readAll
    Response.ok |>.text s!"got: {body}"

  check := fun response => do
    if response.contains "100 Continue" then
      throw <| IO.userError s!"Should NOT have 100 Continue without Expect header:\n{response}"
    unless response.contains "200 OK" do
      throw <| IO.userError s!"Expected 200 OK:\n{response}"
}
