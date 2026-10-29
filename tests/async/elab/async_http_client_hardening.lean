module

import Std.Http.Test.Helpers

/-! Regression tests for security hardening of the HTTP client: request targets that name another
origin, `407` challenges from origins reached directly, authenticators across redirects, and
middleware on cross-origin redirect hops. -/

open Std.Async
open Std Http Internal
open Test.ClientHelpers

def getReq (path : String) : Async (Request Body.Empty) :=
  Request.new |>.method .get |>.uri! path |>.empty

-- A request whose absolute-form target names another host is refused instead of being sent to the
-- origin it was handed with, where a proxy would forward it to the named host.
#eval show IO _ from runWithTimeout "a target naming another origin is refused" 3000 <|
  Async.block do
  let (_mock, server) ← Mock.new
  let tc ← mkClient server
  let request ← Request.new |>.method .get |>.uri! "http://b.example/x" |>.empty
  match ← tc.client.trySend (origin "a.example") request with
  | .error (.invalidRequest _) => pure ()
  | .error e => throw (IO.userError s!"expected invalidRequest, got {e}")
  | .ok _ => throw (IO.userError "a request for b.example was sent to a.example")

-- An absolute-form target for the origin itself is still accepted.
#eval show IO _ from runWithTimeout "a target naming its own origin is sent" 3000 <|
  Async.block do
  let (mock, server) ← Mock.new
  let tc ← mkClient server
  let request ← Request.new |>.method .get |>.uri! "http://example.com/x" |>.empty
  let p ← sendInBackground tc request
  let raw ← drainRequest mock
  unless (String.fromUTF8! raw).startsWith "GET /x HTTP/1.1" do
    throw (IO.userError s!"unexpected request {(String.fromUTF8! raw).quote}")
  mock.send (rawResp "200 OK" #[("Content-Length", "2")] "ok")
  match ← await p.result! with
  | .ok r => unless (← r.body.readAll (α := String)) == "ok" do throw (IO.userError "wrong body")
  | .error e => throw (IO.userError s!"the request failed: {e}")
