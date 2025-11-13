import Std.Internal.Http
import Std.Internal.Async

open Std.Internal.IO.Async
open Std Http

def toByteArray (req : Request (Array Chunk)) (chunked := false) : IO ByteArray := Async.block do
  let mut data := .empty

  data := data ++ (String.toUTF8 <| toString req.head)

  for part in req.body do
    let part := if chunked then Internal.Encode.encode .v11 .empty part |>.toByteArray else part.data
    data := data ++ part

  if chunked then
    data := data ++ Internal.Encode.encode .v11 .empty (Chunk.mk .empty .empty) |>.toByteArray

  return data

def sendRequests
    (client : Mock.Client) (reqs : Array (Request (Array Chunk)))
    (onRequest : Request Body → Async (Response Body)) (chunked : Bool := false) :
    IO ByteArray := Async.block do

  let mut data := .empty

  for req in reqs do
    data := data ++ (← toByteArray req chunked)

  client.enqueueReceive data

  Std.Http.Server.serveConnection client onRequest (config := { lingeringTimeout := 3000 })

  client.getSentData

-- Tests

-- Test basic content-length

#eval do
  let client ← Mock.Client.new

  -- Handler

  let handler := fun (req : Request Body) => do
    if req.head.method == .get ∧
       req.head.version == .v11 ∧
       toString req.head.uri = "/" ∧
       req.head.headers.hasEntry "Host" "example.com" ∧
       req.head.headers.hasEntry "Content-Length" "7"
    then
      return Response.ok "ok"
    else
      return Response.badRequest "invalid"

  -- Sending

  let response ← sendRequests client #[
     Request.new
      |>.method .get
      |>.uri! "/"
      |>.header "Host" (.new "example.com")
      |>.header "Content-Length" (.new "7")
      |>.body #[.mk "pochita".toUTF8 #[]],
  ] handler

  let responseData := String.fromUTF8! response

  assert! responseData = "HTTP/1.1 200 OK\x0d\nContent-Length: 2\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nok"

-- Test basic send

#eval show IO _ from do
  let client ← Mock.Link.new

  -- Handler

  let handler := fun (req : Request Body) => do
    if req.head.method == Method.get ∧
       req.head.version == Version.v11 ∧
       toString req.head.uri = "/" ∧
       req.head.headers.hasEntry "Host" "example.com" ∧
       req.head.headers.hasEntry "Transfer-Encoding" "chunked"
    then
      let stream ← Body.ByteStream.empty

      background do
        discard <| stream.write "ata poxa".toUTF8
        stream.close

      return Response.ok stream
    else
      return Response.badRequest "invalid"

  -- Sending

  let req := Request.new
      |>.method .get
      |>.uri! "/"
      |>.header "Host" (.new "example.com")
      |>.header "Transfer-Encoding" (.new "chunked")
      |>.body #[Chunk.mk "pochita".toUTF8 #[],
                .mk " come açucare".toUTF8 #[]]

  let response ← sendRequests client (chunked := true) #[req] handler
  let responseData := String.fromUTF8! response
  IO.println responseData
