module

import Std.Http.Test.Helpers

/-! Regression tests for HTTP client redirect handling: Post/Redirect/Get to the same URL, and the
outcome of a redirect chain that runs out of hops. -/

open Std.Async
open Std Http Internal
open Test.ClientHelpers

-- Post/Redirect/Get to the same URL: the `GET` the `303` asks for is a different request from the
-- `POST`, so it is not mistaken for a cycle.
#eval show IO _ from runWithTimeout "POST then 303 to its own URL is followed with GET" 3000 <|
  Async.block do
  let (mock, server) ← Mock.new
  let tc ← mkClient server
  let request ← Request.new |>.method .post |>.uri! "/items" |>.text "x=1"
  let p ← sendInBackground tc request
  discard <| drainRequest mock
  mock.send (rawResp "303 See Other" #[("Location", "/items"), ("Content-Length", "0")] "")
  let follow := String.fromUTF8! (← drainRequest mock)
  unless follow.startsWith "GET /items HTTP/1.1" do
    throw (IO.userError s!"the 303 was not followed with GET: {follow.quote}")
  mock.send (rawResp "200 OK" #[("Content-Length", "4")] "list")
  match ← await p.result! with
  | .ok r => unless (← r.body.readAll (α := String)) == "list" do throw (IO.userError "wrong body")
  | .error e => throw (IO.userError s!"the request failed: {e}")

-- A redirect whose body is cut short reports the connection failure itself, which a retry can act
-- on, rather than an untyped I/O error.
#eval show IO _ from runWithTimeout "a truncated redirect body is a typed, retryable error" 3000 <|
  Async.block do
  let (mock, server) ← Mock.new
  let tc ← mkClient server
  let request ← Request.new |>.method .get |>.uri! "/old" |>.empty
  let p : IO.Promise (Except Client.Error (Response Body.Stream)) ← IO.Promise.new
  background do discard <| p.resolve (← tc.client.trySend tc.origin request)
  discard <| drainRequest mock
  mock.send (rawResp "302 Found" #[("Location", "/new"), ("Content-Length", "10")] "12345")
  mock.close
  match ← await p.result! with
  | .error e =>
    unless e.isRetryable do throw (IO.userError s!"expected a retryable error, got {e}")
  | .ok r => throw (IO.userError s!"expected a failure, got {r.line.status.toCode}")
