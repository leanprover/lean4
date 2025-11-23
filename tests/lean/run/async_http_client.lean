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

/--
info: "HTTP/1.1 200 OK\x0d\nContent-Length: 9\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nmaracujá"
-/
#guard_msgs in
#eval
  IO.println =<< Async.block do
    let (client, server) ← Mock.new

    let handler := fun (req : Request Body) => show Async _ from do

      return Response.new
        |>.status .ok
        |>.body req.body

    background (Std.Http.Server.serveConnection server handler (config := { lingeringTimeout := 3000 }))

    let conn ← Http.Client.createPersistentConnection client "localhost"

    let response ← conn.send <| .post (.parse! "/a/b") "maracujá"

    let body := response.body
    let res ← body.collectString

    return s!"{response.head}{res.getD "?"}".quote

/--
info: "HTTP/1.1 200 OK\x0d\nContent-Length: 0\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
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

      return Response.new
        |>.status .ok
        |>.body req.body

    background (Std.Http.Server.serveConnection server handler (config := { lingeringTimeout := 3000 }))

    let conn ← Http.Client.createPersistentConnection client "localhost"

    let response ← conn.send <| .post (.parse! "/a/b") "maracujá"

    let body := response.body
    let res ← body.collectString

    return s!"{response.head}{res.getD "?"}".quote

/--
info: "HTTP/1.1 404 Not Found\x0d\nContent-Length: 9\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\nNot Found"
-/
#guard_msgs in
#eval
  IO.println =<< Async.block do
    let (client, server) ← Mock.new

    let handler := fun (req : Request Body) => show Async _ from do
      if req.head.uri.path?.map toString == "/missing" then
        return Response.new
          |>.status .notFound
          |>.body ("Not Found" : Body)
      else
          return Response.new
          |>.status .ok
          |>.body ("Found" : Body)

    background (Std.Http.Server.serveConnection server handler (config := { lingeringTimeout := 3000 }))

    let conn ← Http.Client.createPersistentConnection client "localhost"

    let response ← conn.send <| .get (.parse! "/missing")

    let body := response.body
    let res ← body.collectString

    return s!"{response.head}{res.getD "?"}".quote

/--
info: "HTTP/1.1 200 OK\x0d\nContent-Length: 13\x0d\nServer: LeanHTTP/1.1\x0d\nContent-Type: application/json\x0d\n\x0d\n{\"key\":\"val\"}"
-/
#guard_msgs in
#eval
  IO.println =<< Async.block do
    let (client, server) ← Mock.new

    let handler := fun (_ : Request Body) => show Async _ from do
      return Response.new
        |>.status .ok
        |>.header! "Content-Type" "application/json"
        |>.body ("{\"key\":\"val\"}" : Body)

    background (Std.Http.Server.serveConnection server handler (config := { lingeringTimeout := 3000 }))

    let conn ← Http.Client.createPersistentConnection client "localhost"

    let response ← conn.send <| .get (.parse! "/json")

    let body := response.body
    let res ← body.collectString

    return s!"{response.head}{res.getD "?"}".quote
