import Std.Internal.Http
import Std.Internal.Http.Client
import Std.Internal.Async

open Std.Internal.IO.Async
open Std Http

abbrev TestHandler := Request Body.Stream → ContextAsync (Response Body.Stream)

instance : Std.Http.Server.Handler TestHandler where
  onRequest handler request := handler request

private def runClientRequest (handler : TestHandler) (request : Async (Request Body.Stream)) : Async String := do
  let (client, server) ← Mock.new

  background (Std.Http.Server.serveConnection server handler
    (config := { lingeringTimeout := 3000, generateDate := false }) |>.run)

  let conn ← Std.Http.Client.createPersistentConnection client
  let response ← conn.send (← request)
  let body : String ← ContextAsync.run response.body.readAll

  conn.close

  return s!"{response.head}{body}".quote

/--
info: "HTTP/1.1 200 OK\x0d\nContent-Length: 9\x0d\nServer: LeanHTTP/1.1\x0d\nmaracujá"
-/
#guard_msgs in
#eval IO.println =<< Async.block do
  runClientRequest
    (handler := fun req => pure { head := { status := .ok }, body := req.body })
    (request :=
      Request.post (.originForm! "/a/b")
      |>.header! "Host" "."
      |>.text "maracujá")

/--
info: "HTTP/1.1 200 OK\x0d\nContent-Length: 0\x0d\nServer: LeanHTTP/1.1\x0d\n"
-/
#guard_msgs in
#eval IO.println =<< Async.block do
  runClientRequest
    (handler := fun req => show ContextAsync _ from do
      let mut size := 0

      for chunk in req.body do
        size := size + chunk.data.size
        if size > 100 then
          return (← Response.withStatus .payloadTooLarge |>.blank)

      Response.ok |>.blank)
    (request :=
      Request.post (.originForm! "/a/b")
      |>.header! "Host" "."
      |>.text "maracujá")

/--
info: "HTTP/1.1 404 Not Found\x0d\nContent-Length: 9\x0d\nServer: LeanHTTP/1.1\x0d\nContent-Type: text/plain; charset=utf-8\x0d\nNot Found"
-/
#guard_msgs in
#eval IO.println =<< Async.block do
  runClientRequest
    (handler := fun req => show ContextAsync _ from do
      if toString req.head.uri == "/missing" then
        Response.notFound |>.text "Not Found"
      else
        Response.ok |>.text "Found")
    (request :=
      Request.get (.originForm! "/missing")
      |>.header! "Host" "localhost"
      |>.noBody)

/--
info: "HTTP/1.1 200 OK\x0d\nContent-Length: 13\x0d\nServer: LeanHTTP/1.1\x0d\nContent-Type: application/json\x0d\n{\"key\":\"val\"}"
-/
#guard_msgs in
#eval IO.println =<< Async.block do
  runClientRequest
    (handler := fun (_ : Request Body.Stream) => show ContextAsync _ from do
      let content := "{\"key\":\"val\"}".toUTF8
      Response.new
        |>.status .ok
        |>.header! "Content-Type" "application/json"
        |>.stream (fun stream => do
          stream.setKnownSize (some (.fixed content.size))
          stream.send (Chunk.ofByteArray content)
          stream.close))
    (request :=
      Request.get (.originForm! "/json")
      |>.header! "Host" "localhost"
      |>.noBody)
