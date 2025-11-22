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
        |>.header! "Connection" "close"
        |>.body Body.zero

    return Response.new
      |>.status .ok
      |>.body "hello robert"

  let response ← sendRequests pair #[
     Request.new
      |>.uri! "/ata/po"
      |>.header! "Content-Length" "4"
      |>.header! "Host" "."
      |>.body #[.mk "test".toUTF8 #[]],
    Request.new
      |>.uri! "/ata/po"
      |>.header! "Content-Length" "13"
      |>.header! "Connection" "close"
      |>.header! "Host" "."
      |>.body #[.mk "testtesttests".toUTF8 #[]],
     Request.new
      |>.uri! "/ata/po"
      |>.header! "Content-Length" "4"
      |>.header! "Host" "."
      |>.body #[.mk "test".toUTF8 #[]],
  ] handler

  let responseData := String.fromUTF8! response
  IO.println <| String.quote responseData

#eval
  IO.println =<< Async.block do
    let (client, server) ← Mock.new

    let handler := fun (req : Request Body) => show Async _ from do
      let mut size := 0

      for i in req.body do
        size := size + i.size
        if size > 100 then
          return Response.new
          |>.status .payloadTooLarge
          |>.header! "Connection" "close"
          |>.body Body.zero


      let res ← do
        match req.body with
        | .stream s => pure <| toString (← s.isClosed)
        | _ => pure "b"

      return Response.new
        |>.status .ok
        |>.body req.body

    background (Std.Http.Server.serveConnection server handler (config := { lingeringTimeout := 3000 }))

    let conn ← Http.Client.createPersistentConnection client "localhost"

    let response ← conn.send <| .post (.parse! "/atata/be") "a faca que corta o fogo"

    let body := response.body
    let res ← body.collectString

    return s!"{response.head}{res.getD "?"}"
