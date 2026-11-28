module

import Std.Http.Test.Helpers

/-! The HTTP client retries final responses whose status is in `Config.retryStatuses`, honouring
`Retry-After` in seconds and capping it at `maxRetryDelay`, and waits `retryDelay`, doubled each
time, before retrying after a connection-level failure. Requests that cannot be sent again whole are
never retried. -/

open Std.Async
open Std Http Internal
open Test.ClientHelpers

/-- A client whose connector hands out `servers` in order and records when each was dialled. -/
def serversClient (servers : Array Mock.Server) (config : Client.Config) (maxRetries : Nat := 1) :
    Async (Client × IO.Ref (Array Nat)) := do
  let next ← IO.mkRef 0
  let dials ← IO.mkRef (#[] : Array Nat)
  let connect : Client.Connector := fun _ _ => do
    dials.modify (·.push 0)
    let now ← IO.monoMsNow
    dials.modify fun ds => ds.pop.push now
    let index ← next.modifyGet fun i => (i, i + 1)
    match servers[index]? with
    | some server => return .ok (.of server)
    | none => return .error (.connect "no more servers")
  return (← Client.new config connect (maxRetries := maxRetries), dials)

def getReq (path : String := "/") (method : Method := .get) : Async (Request Body.Full) :=
  Request.new |>.method method |>.uri! path |>.text ""

def sendAsync (client : Client) (request : Request Body.Full) :
    Async (IO.Promise (Except Client.Error (Response Body.Stream))) := do
  let p ← IO.Promise.new
  background do discard <| p.resolve (← client.trySend (origin "example.com") request)
  return p

def statusOf (p : IO.Promise (Except Client.Error (Response Body.Stream))) : Async (Nat × String) := do
  match ← await p.result! with
  | .ok r => return (r.line.status.toCode.toNat, ← r.body.readAll (α := String))
  | .error e => throw (IO.userError s!"the request failed: {e}")

def unavailable := rawResp "503 Service Unavailable" #[("Content-Length", "4")] "busy"

#eval show IO _ from runWithTimeout "a listed status is retried" 4000 <| Async.block do
  let (m0, s0) ← Mock.new
  let (m1, s1) ← Mock.new
  let (client, dials) ← serversClient #[s0, s1] { retryStatuses := #[.serviceUnavailable] }
  let p ← sendAsync client (← getReq "/r")
  discard <| drainRequest m0
  m0.send unavailable
  discard <| drainRequest m1
  m1.send (rawResp "200 OK" #[("Content-Length", "2")] "ok")
  unless (← statusOf p) == (200, "ok") do throw (IO.userError "the retry was not delivered")
  unless (← dials.get).size == 2 do throw (IO.userError "expected two connections")

#eval show IO _ from runWithTimeout "Retry-After sets the delay before the retry" 5000 <|
  Async.block do
  let (m0, s0) ← Mock.new
  let (m1, s1) ← Mock.new
  let (client, dials) ← serversClient #[s0, s1] { retryStatuses := #[.tooManyRequests] }
  let p ← sendAsync client (← getReq)
  discard <| drainRequest m0
  m0.send (rawResp "429 Too Many Requests" #[("Retry-After", "1"), ("Content-Length", "0")] "")
  discard <| drainRequest m1
  m1.send (rawResp "200 OK" #[("Content-Length", "2")] "ok")
  discard <| statusOf p
  let ds ← dials.get
  unless ds.size == 2 && ds[1]! - ds[0]! ≥ 900 do
    throw (IO.userError s!"the retry did not wait for Retry-After: dials at {ds}")

#eval show IO _ from runWithTimeout "maxRetryDelay caps Retry-After" 4000 <| Async.block do
  let (m0, s0) ← Mock.new
  let (m1, s1) ← Mock.new
  let (client, dials) ← serversClient #[s0, s1]
    { retryStatuses := #[.serviceUnavailable], maxRetryDelay := 100 }
  let p ← sendAsync client (← getReq)
  discard <| drainRequest m0
  m0.send (rawResp "503 Service Unavailable" #[("Retry-After", "3600"), ("Content-Length", "0")] "")
  discard <| drainRequest m1
  m1.send (rawResp "200 OK" #[("Content-Length", "2")] "ok")
  discard <| statusOf p
  let ds ← dials.get
  unless ds.size == 2 && ds[1]! - ds[0]! < 2000 do
    throw (IO.userError s!"Retry-After was not capped: dials at {ds}")

#eval show IO _ from runWithTimeout "the last listed response is the caller's" 4000 <| Async.block do
  let (m0, s0) ← Mock.new
  let (m1, s1) ← Mock.new
  let (client, _) ← serversClient #[s0, s1] { retryStatuses := #[.serviceUnavailable] }
  let p ← sendAsync client (← getReq)
  discard <| drainRequest m0
  m0.send unavailable
  discard <| drainRequest m1
  m1.send unavailable
  unless (← statusOf p) == (503, "busy") do throw (IO.userError "expected the second 503")

#eval show IO _ from runWithTimeout "a POST is not retried on a listed status" 4000 <| Async.block do
  let (m0, s0) ← Mock.new
  let (_, s1) ← Mock.new
  let (client, dials) ← serversClient #[s0, s1] { retryStatuses := #[.serviceUnavailable] }
  let p ← sendAsync client (← getReq "/" .post)
  discard <| drainRequest m0
  m0.send unavailable
  unless (← statusOf p) == (503, "busy") do throw (IO.userError "expected the 503")
  unless (← dials.get).size == 1 do throw (IO.userError "the POST was sent again")

#eval show IO _ from runWithTimeout "an unlisted status is not retried" 4000 <| Async.block do
  let (m0, s0) ← Mock.new
  let (client, dials) ← serversClient #[s0] { retryStatuses := #[.serviceUnavailable] }
  let p ← sendAsync client (← getReq)
  discard <| drainRequest m0
  m0.send (rawResp "500 Internal Server Error" #[("Content-Length", "0")] "")
  unless (← statusOf p).1 == 500 do throw (IO.userError "expected the 500")
  unless (← dials.get).size == 1 do throw (IO.userError "the request was sent again")

#eval show IO _ from runWithTimeout "a connection failure is retried after retryDelay" 4000 <|
  Async.block do
  let (m1, s1) ← Mock.new
  let next ← IO.mkRef 0
  let dials ← IO.mkRef (#[] : Array Nat)
  let connect : Client.Connector := fun _ _ => do
    dials.modify (·.push 0)
    let now ← IO.monoMsNow
    dials.modify fun ds => ds.pop.push now
    if (← next.modifyGet fun i => (i, i + 1)) == 0 then return .error (.connect "refused")
    return .ok (.of s1)
  let client ← Client.new { retryDelay := 300 } connect (maxRetries := 1)
  let p ← sendAsync client (← getReq)
  discard <| drainRequest m1
  m1.send (rawResp "200 OK" #[("Content-Length", "2")] "ok")
  discard <| statusOf p
  let ds ← dials.get
  unless ds.size == 2 && ds[1]! - ds[0]! ≥ 250 do
    throw (IO.userError s!"the retry did not wait retryDelay: dials at {ds}")
