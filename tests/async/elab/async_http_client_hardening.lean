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

def bearer : Header.Value := .ofString! "Bearer SECRET"

-- Only a proxy may ask for proxy credentials: an origin reached directly that answers `407` gets
-- the response back, not the credential.
#eval show IO _ from runWithTimeout "a direct origin's 407 is not answered" 3000 <|
  Async.block do
  let (mock, server) ← Mock.new
  let tc ← mkClient server { authenticator := some (Client.Authenticator.const bearer) }
  let p ← sendInBackground tc (← getReq "/x")
  discard <| drainRequest mock
  mock.send (rawResp "407 Proxy Authentication Required"
    #[("Proxy-Authenticate", "Basic realm=\"p\""), ("Content-Length", "0")] "")
  match ← await p.result! with
  | .ok r => unless r.line.status == .proxyAuthenticationRequired do
      throw (IO.userError s!"expected the 407 back, got {r.line.status.toCode}")
  | .error e => throw (IO.userError s!"the request failed: {e}")
  if let some bytes ← mock.tryRecv? then
    throw (IO.userError s!"the client answered a direct 407: {(String.fromUTF8! bytes).quote}")

-- A `401` on the hop after a same-origin redirect is answered: the redirected request's empty body
-- can be replayed.
#eval show IO _ from runWithTimeout "a 401 after a redirect is answered" 3000 <|
  Async.block do
  let (mock, server) ← Mock.new
  let tc ← mkClient server { authenticator := some (Client.Authenticator.const bearer) }
  let p ← sendInBackground tc (← getReq "/old")
  discard <| drainRequest mock
  mock.send (rawResp "302 Found" #[("Location", "/new"), ("Content-Length", "0")] "")
  discard <| drainRequest mock
  mock.send (rawResp "401 Unauthorized"
    #[("WWW-Authenticate", "Bearer"), ("Content-Length", "0")] "")
  let retry := String.fromUTF8! (← drainRequest mock)
  unless retry.startsWith "GET /new" && retry.contains "Authorization: Bearer SECRET" do
    throw (IO.userError s!"the 401 was not answered: {retry.quote}")
  mock.send (rawResp "200 OK" #[("Content-Length", "2")] "ok")
  match ← await p.result! with
  | .ok r => unless (← r.body.readAll (α := String)) == "ok" do throw (IO.userError "wrong body")
  | .error e => throw (IO.userError s!"the request failed: {e}")

-- `Authenticator.const` does not hand its credential to an origin a redirect led to.
#eval show IO _ from runWithTimeout "const does not answer a redirect target's 401" 3000 <|
  Async.block do
  let (mockA, serverA) ← Mock.new
  let (mockB, serverB) ← Mock.new
  let (tc, _) ← mkFollowingClient #[serverA, serverB]
    { authenticator := some (Client.Authenticator.const bearer) }
  let p ← sendInBackground tc (← getReq "/start")
  discard <| drainRequest mockA
  mockA.send (rawResp "302 Found"
    #[("Location", "http://evil.example/steal"), ("Content-Length", "0")] "")
  let hop := String.fromUTF8! (← drainRequest mockB)
  mockB.send (rawResp "401 Unauthorized" #[("WWW-Authenticate", "Bearer"), ("Content-Length", "0")] "")
  match ← await p.result! with
  | .ok r => unless r.line.status == .unauthorized do
      throw (IO.userError s!"expected the 401 back, got {r.line.status.toCode}")
  | .error e => throw (IO.userError s!"the request failed: {e}")
  if hop.contains "Authorization" then
    throw (IO.userError s!"the redirect hop carried credentials: {hop.quote}")
  if let some bytes ← mockB.tryRecv? then
    throw (IO.userError s!"the credential was sent to the redirect target: {(String.fromUTF8! bytes).quote}")

/-- A middleware that adds `Authorization: Bearer SECRET` to every request it sees. -/
def addBearer : Client.Middleware := fun _ req next =>
  next { req with line := { req.line with headers := req.line.headers.insert .authorization bearer } }

/-- Sends a request through `middleware`, has `api.example.com` redirect it to `evil.example`, and
returns what each hop put on the wire. -/
def redirectedThrough (middleware : Client.Middleware) : Async (String × String) := do
  let (mockA, serverA) ← Mock.new
  let (mockB, serverB) ← Mock.new
  let servers := #[serverA, serverB]
  let next ← IO.mkRef 0
  let connect : Client.Connector := fun origin config => do
    let some server := servers[← next.modifyGet fun i => (i, i + 1)]?
      | throw (IO.userError "too many connections")
    return .ok (← Client.Connection.new server origin config)
  let client ← Client.new {} connect (maxRetries := 0) (middlewares := #[middleware])
  let request ← getReq "/start"
  let p : IO.Promise (Except Client.Error (Response Body.Stream)) ← IO.Promise.new
  background do discard <| p.resolve (← client.trySend (origin "api.example.com") request)
  let first := String.fromUTF8! (← drainRequest mockA)
  mockA.send (rawResp "302 Found"
    #[("Location", "http://evil.example/steal"), ("Content-Length", "0")] "")
  let second := String.fromUTF8! (← drainRequest mockB)
  mockB.send (rawResp "200 OK" #[("Content-Length", "0")] "")
  discard <| await p.result!
  return (first, second)

-- A middleware is told which origin each hop goes to, redirect hops included.
#eval show IO _ from runWithTimeout "a middleware sees each hop's origin" 3000 <|
  Async.block do
  let seen ← IO.mkRef (#[] : Array String)
  let record : Client.Middleware := fun hopOrigin req next => do
    seen.modify (·.push (toString hopOrigin))
    next req
  discard <| redirectedThrough record
  let origins ← seen.get
  unless origins == #["http://api.example.com", "http://evil.example"] do
    throw (IO.userError s!"unexpected hop origins {origins}")

-- `Middleware.forOrigin` keeps a credential-adding middleware on its own origin, so a redirect to
-- another host does not carry the credential there.
#eval show IO _ from runWithTimeout "a credential middleware scoped to its origin stays there" 3000 <|
  Async.block do
  let (first, second) ← redirectedThrough (Client.Middleware.forOrigin (origin "api.example.com") addBearer)
  unless first.contains "Authorization: Bearer SECRET" do
    throw (IO.userError s!"the first hop lacked the credential: {first.quote}")
  if second.contains "Authorization" then
    throw (IO.userError s!"the credential followed the redirect: {second.quote}")
