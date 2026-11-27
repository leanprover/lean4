module

import Std.Http.Test.Helpers

/-! A client's `Interceptor` runs on every hop: `onRequest` rewrites each request before it goes (or
fails it), `onResponse` sees each final response head, redirects included, and `onInformational`
sees informational responses such as `103 Early Hints`. `Config.redirectPolicy` keeps the redirects
it declines for the caller. -/

open Std.Async
open Std Http Internal
open Test.ClientHelpers

def getReq (path : String := "/") : Async (Request Body.Empty) :=
  Request.new |>.method .get |>.uri! path |>.empty

#eval show IO _ from runWithTimeout "onRequest rewrites every hop" 3000 <| Async.block do
  let (mock, server) ← Mock.new
  let hops ← IO.mkRef 0
  let interceptor : Client.Interceptor := {
    onRequest := fun _ head => do
      let n ← hops.modifyGet fun n => (n + 1, n + 1)
      return .ok { head with headers := head.headers.insert (.mk "x-hop") (.ofString! (toString n)) } }
  let tc ← mkClient server { interceptor := some interceptor }
  let p ← sendInBackground tc (← getReq "/old")
  let first := String.fromUTF8! (← drainRequest mock)
  mock.send (rawResp "302 Found" #[("Location", "/new"), ("Content-Length", "0")] "")
  let second := String.fromUTF8! (← drainRequest mock)
  mock.send (rawResp "200 OK" #[("Content-Length", "2")] "ok")
  match ← await p.result! with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"the request failed: {e}")
  unless first.toLower.contains "x-hop: 1" && second.startsWith "GET /new " &&
      second.toLower.contains "x-hop: 2" do
    throw (IO.userError s!"the hops were not rewritten:\n{first.quote}\n{second.quote}")

#eval show IO _ from runWithTimeout "an onRequest failure fails the request unsent" 3000 <|
  Async.block do
  let (_mock, server) ← Mock.new
  let interceptor : Client.Interceptor := {
    onRequest := fun _ _ => pure (.error (.invalidRequest "blocked")) }
  let tc ← mkClient server { interceptor := some interceptor }
  match ← tc.client.trySend tc.origin (← getReq) with
  | .error (.invalidRequest "blocked") => pure ()
  | .error e => throw (IO.userError s!"expected the interceptor's error, got {e}")
  | .ok _ => throw (IO.userError "the blocked request succeeded")

#eval show IO _ from runWithTimeout "onResponse and onInformational see every head" 3000 <|
  Async.block do
  let (mock, server) ← Mock.new
  let seen ← IO.mkRef (#[] : Array String)
  let done ← IO.Promise.new
  let interceptor : Client.Interceptor := {
    onResponse := fun _ request head => do
      seen.modify (·.push s!"{request.uri} {head.status.toCode}")
      if head.status == .ok then done.resolve ()
    onInformational := fun _ request head =>
      seen.modify (·.push s!"{request.uri} info {head.status.toCode}") }
  let tc ← mkClient server { interceptor := some interceptor }
  let p ← sendInBackground tc (← getReq "/old")
  discard <| drainRequest mock
  mock.send (rawResp "302 Found" #[("Location", "/new"), ("Content-Length", "0")] "")
  discard <| drainRequest mock
  mock.send "HTTP/1.1 103 Early Hints\r\nLink: </style.css>; rel=preload\r\n\r\n".toUTF8
  mock.send (rawResp "200 OK" #[("Content-Length", "2")] "ok")
  match ← await p.result! with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"the request failed: {e}")
  await done.result!
  -- The hooks run in the background, so the informational one may land after the final head.
  IO.sleep 50
  let got := (← seen.get).qsort (· < ·)
  unless got == #["/new 200", "/new info 103", "/old 302"] do
    throw (IO.userError s!"unexpected heads seen: {got}")

#eval show IO _ from runWithTimeout "a declined redirect is the caller's" 3000 <| Async.block do
  let (mock, server) ← Mock.new
  let sameOrigin : Client.RedirectPolicy := fun current _ _ plan => plan.origin == current
  let tc ← mkClient server { redirectPolicy := some sameOrigin }
  let p ← sendInBackground tc (← getReq "/")
  discard <| drainRequest mock
  mock.send (rawResp "302 Found" #[("Location", "http://elsewhere.example/x"), ("Content-Length", "0")] "")
  match ← await p.result! with
  | .ok r => unless r.line.status == .found do
      throw (IO.userError s!"expected the 302, got {r.line.status.toCode}")
  | .error e => throw (IO.userError s!"the request failed: {e}")
