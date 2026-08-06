module

import Std.Http.Test.Helpers

/-!
# HTTP Client Security Tests

Tests for security properties of the HTTP client:

- `Authorization` is stripped on cross-scheme redirects (same host+port, different scheme).
  Before the fix `crossOrigin` checked host+port only; a http→https redirect to the same
  host+port would silently keep the credential header.

- Streaming (`.outgoing`) request bodies must not be retried on connection failure.
  A channel-backed body is consumed on first use; retrying would send an empty body.
-/

open Std.Async
open Std Http Internal
open Test.ClientHelpers

-- ============================================================
-- Redirect: Authorization stripped on scheme-change redirect
-- ============================================================
-- A 302 redirect from http://example.com:443/ to https://example.com:443/r has the
-- same host and port but a different scheme.  crossOrigin must be true so that the
-- Authorization header is stripped before the redirect request is sent.
-- ============================================================

#eval show IO _ from runWithTimeout "scheme-change strips Authorization" 4000 <| Async.block do
  let (mockClient1, mockServer1) ← Mock.new
  let (mockClient2, mockServer2) ← Mock.new
  let connection1 ← Client.Connection.new mockServer1 (config := {})
  let some domain := URI.DomainName.ofString? "example.com"
    | throw (IO.userError "DomainName parse failed")

  -- Agent with scheme=http on port 443. Redirect target https://example.com:443/r
  -- has same host+port but different scheme → crossOrigin is true and the agent
  -- opens a fresh connection via its connector.
  let agent : Client.Agent := {
    connection := connection1
    origin := { scheme := URI.Scheme.ofString! "http", host := .name domain, port := 443 }
    crossOrigin := .follow fun _ => do
      return .ok (← Client.Connection.new mockServer2 (config := {}))
  }

  let request ← Request.new
    |>.method .get
    |>.uri! "/"
    |>.header! "Host" "example.com:443"
    |>.header! "Authorization" "Bearer secret-token"
    |>.empty

  let resultPromise : IO.Promise (Except String (Response Body.Stream)) ← IO.Promise.new
  background do
    let result : Except String (Response Body.Stream) ← try
        let resp ← Client.Agent.send agent request
        pure (Except.ok resp)
      catch e => pure (Except.error (toString e))
    discard <| resultPromise.resolve result

  -- Drain the whole request: reading a single chunk could leave the tail of request 1 to be
  -- picked up below as if it were the redirected request, and the strip check would then pass
  -- against bytes that never carried a header block at all.
  let _ ← drainRequest mockClient1
  mockClient1.send (rawResp "302 Found"
    #[("Location", "https://example.com:443/redirected"),
      ("Content-Length", "0"),
      ("Connection", "close")] "")

  -- Second exchange on mock 2: the redirected request reaches the fresh connection.
  let redirectBytes ← drainRequest mockClient2
  mockClient2.send (rawResp "200 OK"
    #[("Content-Length", "2"), ("Connection", "close")] "ok")

  -- Wait for the agent to finish.
  match ← await resultPromise.result! with
  | Except.error e => throw (IO.userError s!"agent error: {e}")
  | Except.ok _ => pure ()

  let redirectText := String.fromUTF8! redirectBytes
  if redirectText.contains "Authorization:" then
    throw <| IO.userError
      s!"Test 'scheme-change strips Authorization' FAILED: \
         Authorization header present in redirect request\n{redirectText.quote}"

-- ============================================================
-- Redirect: Authorization preserved on same-origin redirect
-- ============================================================
-- A 302 redirect to the same scheme, host, and port is a same-origin redirect.
-- The Authorization header must NOT be stripped in this case.
-- ============================================================

#eval show IO _ from runWithTimeout "same-origin preserves Authorization" 3000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let agent ← mkAgent mockServer

  let request ← Request.new
    |>.method .get
    |>.uri! "/"
    |>.header! "Host" "example.com"
    |>.header! "Authorization" "Bearer secret-token"
    |>.empty

  let resultPromise : IO.Promise (Except String (Response Body.Stream)) ← IO.Promise.new
  background do
    let result : Except String (Response Body.Stream) ← try
        let resp ← Client.Agent.send agent request
        pure (Except.ok resp)
      catch e => pure (Except.error (toString e))
    discard <| resultPromise.resolve result

  -- First exchange: reply with 302 to same scheme+host+port.
  let _ ← drainRequest mockClient
  mockClient.send (rawResp "302 Found"
    #[("Location", "http://example.com/same-origin"),
      ("Content-Length", "0"),
      ("Connection", "keep-alive")] "")

  -- Second exchange: receive the redirected request.
  let redirectBytes ← drainRequest mockClient
  mockClient.send (rawResp "200 OK"
    #[("Content-Length", "2"), ("Connection", "close")] "ok")

  match ← await resultPromise.result! with
  | Except.error e => throw (IO.userError s!"agent error: {e}")
  | Except.ok _ => pure ()

  let redirectText := String.fromUTF8! redirectBytes
  unless redirectText.contains "Authorization:" do
    throw <| IO.userError
      s!"Test 'same-origin preserves Authorization' FAILED: \
         Authorization header was stripped on same-origin redirect\n{redirectText.quote}"

-- ============================================================
-- Body.Any construction
-- ============================================================
-- Verifies that Body.Any can be constructed from any Body implementation.
-- The behavioral property that streaming bodies are consumed on first recv
-- (and thus cannot be replayed) is exercised end-to-end by the 307 redirect test below.
-- ============================================================

#eval show IO _ from Async.block do
  -- Body.Stream: a zero-buffer rendezvous channel.
  let stream ← Body.mkStream
  stream.close
  let _ : Body.Any := Body.Any.ofBody stream

  -- Body.Full: consumed on first recv.
  let full ← Body.Full.ofByteArray "hello".toUTF8
  let _ : Body.Any := Body.Any.ofBody full

  -- Body.Empty: trivially closed.
  let _ : Body.Any := Body.Any.ofBody Body.Empty.mk

-- ============================================================
-- Redirect: non-HTTP/HTTPS scheme in Location is not followed
-- ============================================================
-- A 302 response with Location: ftp://internal-host/secret must not be followed.
-- Before the fix, decideRedirect accepted any scheme that RequestTarget.parse? could
-- parse and would try to connect to the ftp host on port 80 (SSRF).
-- After the fix, only http:// and https:// redirect targets are followed; everything
-- else returns the 3xx response as-is.
-- ============================================================

-- Both tests give the agent a `.follow` policy that records the origin it is asked to dial and
-- refuses. The default `.stop` would return any cross-host 3xx unfollowed on its own, so the
-- status alone proves nothing about the scheme guard — the SSRF regression is a *dial* that must
-- never happen, and only a policy that could have dialled can witness its absence.

#eval show IO _ from runWithTimeout "ftp:// redirect not followed" 3000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let dialed ← IO.mkRef (none : Option String)
  let agent := { ← mkAgent mockServer with
    crossOrigin := .follow fun origin => do
      dialed.set (some s!"{origin.scheme.val}://{origin.host}:{origin.port}")
      return .error (.connect "the redirect target must never be dialled") }

  let request ← Request.new
    |>.method .get
    |>.uri! "/"
    |>.header! "Host" "example.com"
    |>.empty

  let resultPromise ← sendInBackground agent request

  -- Server replies with a redirect to ftp:// (non-HTTP scheme).
  let _ ← drainRequest mockClient
  mockClient.send (rawResp "302 Found"
    #[("Location", "ftp://internal-host/secret"),
      ("Content-Length", "0"), ("Connection", "keep-alive")] "")

  match ← await resultPromise.result! with
  | Except.error e => throw (IO.userError s!"agent error: {e}")
  | Except.ok resp =>
    resp.body.close
    -- The agent must return the 302 as-is, not follow it.
    unless resp.line.status == .found do
      throw <| IO.userError
        s!"Test 'ftp:// redirect not followed' FAILED: expected 302, got {resp.line.status.toCode}"
  if let some target ← dialed.get then
    throw <| IO.userError s!"an ftp:// redirect target was dialled: {target}"

#eval show IO _ from runWithTimeout "file:// redirect not followed" 3000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let dialed ← IO.mkRef (none : Option String)
  let agent := { ← mkAgent mockServer with
    crossOrigin := .follow fun origin => do
      dialed.set (some s!"{origin.scheme.val}://{origin.host}:{origin.port}")
      return .error (.connect "the redirect target must never be dialled") }

  let request ← Request.new
    |>.method .get
    |>.uri! "/"
    |>.header! "Host" "example.com"
    |>.empty

  let resultPromise ← sendInBackground agent request

  let _ ← drainRequest mockClient
  mockClient.send (rawResp "301 Moved Permanently"
    #[("Location", "file:///etc/passwd"),
      ("Content-Length", "0"), ("Connection", "keep-alive")] "")

  match ← await resultPromise.result! with
  | Except.error e => throw (IO.userError s!"agent error: {e}")
  | Except.ok resp =>
    resp.body.close
    unless resp.line.status == .movedPermanently do
      throw <| IO.userError
        s!"Test 'file:// redirect not followed' FAILED: expected 301, got {resp.line.status.toCode}"
  if let some target ← dialed.get then
    throw <| IO.userError s!"a file:// redirect target was dialled: {target}"

-- ============================================================
-- Redirect: https:// is not blocked by the scheme guard
-- ============================================================
-- The SSRF guard in `decideRedirect` admits exactly http and https, so an `https://` Location must
-- reach the redirect machinery. Whether it is then followed is the cross-origin policy's call:
-- `https://example.com/page` resolves to port 443, so it leaves an agent's `http://example.com:80`
-- origin. These two tests pin down both halves — a standalone agent stops and reports the 3xx, and
-- a policy that can open a connection carries the hop through to the https origin.
-- ============================================================

#eval show IO _ from
  runWithTimeout "https:// redirect stops at a standalone agent" 3000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let agent ← mkAgent mockServer

  let request ← Request.new
    |>.method .get
    |>.uri! "/"
    |>.header! "Host" "example.com"
    |>.empty

  let resultPromise ← sendInBackground agent request

  let _ ← drainRequest mockClient
  mockClient.send (rawResp "302 Found"
    #[("Location", "https://example.com/page"), ("Content-Length", "0")] "")

  match ← await resultPromise.result! with
  | Except.error e => throw (IO.userError s!"agent error: {e}")
  | Except.ok resp =>
    resp.body.close
    unless resp.line.status.toCode == 302 do
      throw <| IO.userError
        s!"expected the cross-origin 302 back unfollowed, got {resp.line.status.toCode}"

  -- Nothing may go out on the old connection: the hop needs one of its own.
  IO.sleep 100
  if let some bytes ← mockClient.tryRecv? then
    throw <| IO.userError
      s!"a cross-origin hop was written to the http connection:\n{(String.fromUTF8! bytes).quote}"

#eval show IO _ from
  runWithTimeout "https:// redirect is followed when a connection can be opened" 5000 <|
  Async.block do
  let (mockClient1, mockServer1) ← Mock.new
  let (mockClient2, mockServer2) ← Mock.new
  let (agent, dialled) ← mkFollowingAgent #[mockServer1, mockServer2]

  let request ← Request.new |>.method .get |>.uri! "/"
    |>.header! "Host" "example.com" |>.empty
  let resultPromise ← sendInBackground agent request

  let _ ← drainRequest mockClient1
  mockClient1.send (rawResp "302 Found"
    #[("Location", "https://example.com/page"), ("Content-Length", "0"),
      ("Connection", "keep-alive")] "")

  let secondBytes ← drainRequest mockClient2
  mockClient2.send (rawResp "200 OK" #[("Content-Length", "2"), ("Connection", "close")] "ok")

  match ← await resultPromise.result! with
  | Except.error e => throw (IO.userError s!"https redirect failed: {e}")
  | Except.ok resp =>
    let body ← resp.body.readAll (α := String)
    unless body == "ok" do throw <| IO.userError s!"expected 'ok', got {body.quote}"

  -- The hop must be dialled at the https origin, and carry its path.
  let some target := (← dialled.get)[0]?
    | throw (IO.userError "the https hop never opened a connection")
  unless target.scheme.val == "https" do
    throw <| IO.userError s!"the hop was dialled with scheme {target.scheme.val.quote}"
  unless target.port == 443 do
    throw <| IO.userError s!"the hop was dialled at port {target.port}, expected 443"
  let secondText := String.fromUTF8! secondBytes
  unless secondText.startsWith "GET /page" do
    throw <| IO.userError s!"second hop did not request /page:\n{secondText.quote}"

-- ============================================================
-- Redirect: non-replayable body blocks auto-follow of 307
-- ============================================================
-- RFC 9110 §15.4.8: the user agent MUST NOT automatically redirect a 307 when
-- the request body cannot be repeated.  A streaming channel body (.stream) is
-- consumed on first use and therefore non-replayable.  The agent must surface
-- the 307 response unchanged so the caller can decide what to do next, rather
-- than silently following the redirect with an empty (or wrong) body.
-- ============================================================

#eval show IO _ from runWithTimeout "streaming body dropped on 307 redirect" 3000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let agent ← mkAgent mockServer

  let request ← Request.new
    |>.method .put
    |>.uri! "/upload"
    |>.header! "Host" "example.com"
    |>.stream (fun out => do
        out.send (Chunk.ofByteArray "payload".toUTF8)
        out.close)

  let resultPromise : IO.Promise (Except String (Response Body.Stream)) ← IO.Promise.new

  background do
    let result ← try
        let resp ← Client.Agent.send agent request
        pure (Except.ok resp)
      catch e => pure (Except.error (toString e))
    discard <| resultPromise.resolve result

  -- First request: drain it completely before replying with 307.
  -- The body may be Transfer-Encoding: chunked (ends with "0\r\n\r\n") or
  -- Content-Length (ends with the body bytes) depending on whether the body
  -- stream was already closed when the H1 machine flushed the headers.
  -- Accept either encoding to avoid a scheduling-dependent flake.
  let mut firstBytes := ByteArray.empty
  repeat
    let some chunk ← mockClient.recv?
      | throw (IO.userError "Test failed: connection closed before first request")
    firstBytes := firstBytes ++ chunk
    let t := String.fromUTF8! firstBytes
    if t.endsWith "0\r\n\r\n" || t.endsWith "payload" then break
  mockClient.send (rawResp "307 Temporary Redirect"
    #[("Location", "/new-upload"),
      ("Content-Length", "0")] "")

  -- RFC 9110 §15.4.8: the agent must NOT follow the 307 automatically because
  -- the streaming body cannot be replayed.  The 307 is returned directly to the
  -- caller; no second request reaches the mock server.
  match ← await resultPromise.result! with
  | Except.error e => throw (IO.userError s!"agent error: {e}")
  | Except.ok resp =>
    resp.body.close
    unless resp.line.status.toCode == 307 do
      throw <| IO.userError
        s!"Test 'streaming body dropped on 307 redirect' FAILED: \
           expected 307 (no auto-redirect for non-replayable body), \
           got {resp.line.status.toCode}"
