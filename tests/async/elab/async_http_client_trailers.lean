module

import Std.Http.Test.Helpers

/-! `Response.trailers` gives the trailer fields that ended a chunked response body the client
received, without those a trailer may not carry (RFC 9110 §6.5.1); a body without trailers gives
`none`, and the trailers of one response do not carry over to the next on the same connection. -/

open Std.Async
open Std Http Internal
open Test.ClientHelpers

def getReq (path : String := "/") : Async (Request Body.Empty) :=
  Request.new |>.method .get |>.uri! path |>.empty

def response (p : IO.Promise (Except String (Response Body.Stream))) : Async (Response Body.Stream) := do
  match ← await p.result! with
  | .ok r => pure r
  | .error e => throw (IO.userError s!"the request failed: {e}")

#eval show IO _ from runWithTimeout "trailers are handed to the caller" 3000 <| Async.block do
  let (mock, server) ← Mock.new
  let tc ← mkClient server
  let p ← sendInBackground tc (← getReq)
  discard <| drainRequest mock
  mock.send (rawResp "200 OK" #[("Transfer-Encoding", "chunked")]
    "2\r\nok\r\n0\r\nX-Checksum: abc\r\nContent-Length: 99\r\n\r\n")
  let r ← response p
  unless (← r.body.readAll (α := String)) == "ok" do throw (IO.userError "wrong body")
  match ← await r.trailers with
  | some fields =>
    unless (fields.get? (.mk "x-checksum")).map (·.value) == some "abc" do
      throw (IO.userError "X-Checksum is missing")
    if fields.contains .contentLength then throw (IO.userError "a framing field was kept")
  | none => throw (IO.userError "no trailers")

#eval show IO _ from runWithTimeout "a body without trailers gives none" 3000 <| Async.block do
  let (mock, server) ← Mock.new
  let tc ← mkClient server
  let p ← sendInBackground tc (← getReq)
  discard <| drainRequest mock
  mock.send (rawResp "200 OK" #[("Content-Length", "2")] "ok")
  let r ← response p
  discard <| r.body.readAll (α := String)
  if (← await r.trailers).isSome then throw (IO.userError "trailers out of nowhere")

#eval show IO _ from runWithTimeout "trailers do not carry over to the next response" 3000 <|
  Async.block do
  let (mock, server) ← Mock.new
  let tc ← mkClient server
  let p1 ← sendInBackground tc (← getReq "/1")
  discard <| drainRequest mock
  mock.send (rawResp "200 OK" #[("Transfer-Encoding", "chunked")] "1\r\na\r\n0\r\nX-One: 1\r\n\r\n")
  let r1 ← response p1
  discard <| r1.body.readAll (α := String)
  let p2 ← sendInBackground tc (← getReq "/2")
  discard <| drainRequest mock
  mock.send (rawResp "200 OK" #[("Transfer-Encoding", "chunked")] "1\r\nb\r\n0\r\n\r\n")
  let r2 ← response p2
  discard <| r2.body.readAll (α := String)
  if let some fields := ← await r2.trailers then
    unless fields.isEmpty do throw (IO.userError "the first response's trailers carried over")
