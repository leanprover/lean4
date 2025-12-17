import Std.Internal.Http
import Std.Internal.Async.TCP
import Std.Time
import Std.Data.Iterators

open Std.Internal.IO.Async
open Std.Http
open Std Iterators

def theTimeInTheFuture : Async ByteArray := do
  (← Sleep.mk 1000).wait
  return s!"?\n".toUTF8

def tick :=
  Iter.repeat (fun _ => ()) () |>.mapM (fun _ => theTimeInTheFuture)

def writeToStream (s : Body.ByteStream) {α : Type} [Iterator α Async ByteArray] [IteratorLoop α Async Async]
    (i : Std.IterM (α := α) Async ByteArray) (count : Nat) : Async Unit := do
  let mut n := 0
  for b in i.allowNontermination do
    if n >= count then break
    s.writeChunk (Chunk.mk b #[("time", some (toString n))])
    n := n + 1
  s.close

/-- Convert an HTTP request to a byte array -/
def requestToByteArray (req : Request (Array Chunk)) : IO ByteArray := Async.block do
  let mut data := String.toUTF8 <| toString req.head
  for part in req.body do data := data ++ part.data
  return data

/-- Send a request through a mock connection and return the response data -/
def sendRequest (client : Mock.Client) (server : Mock.Server) (req : Request (Array Chunk))
    (onRequest : Request Body → ContextAsync (Response Body)) : IO ByteArray := Async.block do
  let data ← requestToByteArray req

  client.send data
  Std.Http.Server.serveConnection server onRequest (config := { lingeringTimeout := 3000, keepAliveTimeout := ⟨1000, by decide⟩ })
    |>.run

  let res ← client.recv?
  pure <| res.getD .empty

def testStreamingResponse : IO Unit := do
  let pair ← Mock.new
  let (client, server) := pair

  let request := Request.new
    |>.method .get
    |>.uri! "/stream"
    |>.header! "Host" "localhost"
    |>.header! "Connection" "close"
    |>.body #[]

  let response ← sendRequest client server request handle
  let responseData := String.fromUTF8! response

  IO.println responseData.quote

  -- Check that response starts with correct HTTP status line
  if !responseData.startsWith "HTTP/1.1 200 OK\x0d\n" then
    throw <| IO.userError "Response should start with HTTP/1.1 200 OK"

  -- Check that Transfer-Encoding header is present (for streaming)
  if !responseData.contains "Transfer-Encoding: chunked" then
    throw <| IO.userError "Response should use chunked transfer encoding"

  -- Check that we got multiple chunks (at least 3 time stamps)
  let bodyStart := responseData.splitOn "\x0d\n\x0d\n"
  if bodyStart.length < 2 then
    throw <| IO.userError "Response should have headers and body"
where
  handle (_req : Request Body) : ContextAsync (Response Body) :=
    Response.new
      |>.status .ok
      |>.stream (writeToStream · tick 3)

/--
info: "HTTP/1.1 200 OK\x0d\nTransfer-Encoding: chunked\x0d\nConnection: close\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n2;time=0\x0d\n?\n\x0d\n2;time=1\x0d\n?\n\x0d\n2;time=2\x0d\n?\n\x0d\n0\x0d\n\x0d\n"
-/
#guard_msgs in
#eval testStreamingResponse

/-- Test that without Connection: close, the server waits and times out -/
def testTimeout : IO Unit := do
  let pair ← Mock.new
  let (client, server) := pair

  -- Request WITHOUT Connection: close header
  let request := Request.new
    |>.method .get
    |>.uri! "/stream"
    |>.header! "Host" "localhost"
    |>.body #[]

  let response ← sendRequest client server request handle
  let responseData := String.fromUTF8! response

  IO.println responseData.quote
where
  handle (_req : Request Body) : ContextAsync (Response Body) :=
    return Response.new
      |>.status .ok
      |>.build

/--
info: "HTTP/1.1 200 OK\x0d\nContent-Length: 0\x0d\nServer: LeanHTTP/1.1\x0d\n\x0d\n"
-/
#guard_msgs in
#eval testTimeout
