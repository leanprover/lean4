module

import Std.Http.Test.Helpers

/-! Cancelling a request through the `CancellationContext` given to `Client.trySend`: before its
response it fails with `Error.cancelled` and its connection closes, also while it waits for a
connection; after its response head it has no effect. -/

open Std.Async
open Std Http Internal
open Test.ClientHelpers

def getReq (path : String := "/") : Async (Request Body.Empty) :=
  Request.new |>.method .get |>.uri! path |>.empty

def sendCancellable (client : Client) (path : String) (ctx : CancellationContext) :
    Async (IO.Promise (Except Client.Error (Response Body.Stream))) := do
  let p ← IO.Promise.new
  let request ← getReq path
  background do
    discard <| p.resolve (← client.trySend (origin "example.com") request (cancel := some ctx))
  return p

#eval show IO _ from runWithTimeout "a request cancelled before its response fails" 3000 <|
  Async.block do
  let (mock, server) ← Mock.new
  let tc ← mkClient server
  let ctx ← CancellationContext.new
  let p ← sendCancellable tc.client "/slow" ctx
  discard <| drainRequest mock
  ctx.cancel .cancel
  match ← await p.result! with
  | .error .cancelled => pure ()
  | .error e => throw (IO.userError s!"expected .cancelled, got {e}")
  | .ok _ => throw (IO.userError "the cancelled request succeeded")
  -- Its connection is closed: the peer reads the end of the stream.
  unless (← mock.recv?).isNone do throw (IO.userError "the connection stayed open")

#eval show IO _ from runWithTimeout "a request cancelled while waiting for a connection fails" 3000 <|
  Async.block do
  let (mock, server) ← Mock.new
  let tc ← mkClient server { maxConnectionsPerOrigin := ⟨1, by decide⟩ }
  let first ← sendInBackground tc (← getReq "/first")
  discard <| drainRequest mock
  let ctx ← CancellationContext.new
  let waiting ← sendCancellable tc.client "/waiting" ctx
  IO.sleep 50
  ctx.cancel .cancel
  match ← await waiting.result! with
  | .error .cancelled => pure ()
  | .error e => throw (IO.userError s!"expected .cancelled, got {e}")
  | .ok _ => throw (IO.userError "the cancelled request succeeded")
  -- The request in flight is untouched, and its connection carries the next one.
  mock.send (rawResp "200 OK" #[("Content-Length", "2")] "ok")
  match ← await first.result! with
  | .ok r => unless (← r.body.readAll (α := String)) == "ok" do throw (IO.userError "wrong body")
  | .error e => throw (IO.userError s!"the first request failed: {e}")
  let third ← sendInBackground tc (← getReq "/third")
  let wire := String.fromUTF8! (← drainRequest mock)
  unless wire.startsWith "GET /third " do
    throw (IO.userError s!"the cancelled request went out: {wire.quote}")
  mock.send (rawResp "200 OK" #[("Content-Length", "1")] "3")
  match ← await third.result! with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"the third request failed: {e}")

#eval show IO _ from runWithTimeout "cancelling after the response head has no effect" 3000 <|
  Async.block do
  let (mock, server) ← Mock.new
  let tc ← mkClient server
  let ctx ← CancellationContext.new
  let p ← sendCancellable tc.client "/" ctx
  discard <| drainRequest mock
  mock.send (rawResp "200 OK" #[("Content-Length", "5")] "hello")
  let response ← match ← await p.result! with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"the request failed: {e}")
  ctx.cancel .cancel
  unless (← response.body.readAll (α := String)) == "hello" do throw (IO.userError "wrong body")
