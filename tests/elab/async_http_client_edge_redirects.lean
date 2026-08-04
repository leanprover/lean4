module

import Std.Http.Test.Helpers

open Std.Async
open Std Http Internal
open Test.ClientHelpers

/-! HTTP client redirect rewriting, security, policy, and target-resolution edge cases. -/

-- ============================================================
-- Section 1 — Redirect method/body rewrites (RFC 9110 §15.4)
-- ============================================================

-- 303 See Other: any method → GET, body dropped.
-- The existing tests cover 302 POST→GET; this one covers the non-POST path.

#eval show IO _ from runWithTimeout "303 See Other converts PUT to GET and drops body" 3000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let agent ← mkAgent mockServer

  let request ← Request.new
    |>.method .put
    |>.uri! "/upload"
    |>.header! "Host" "example.com"
    |>.text "original-body"

  let resultPromise ← sendInBackground agent request

  let _ ← drainRequest mockClient
  mockClient.send (rawResp "303 See Other"
    #[("Location", "/after-put"),
      ("Content-Length", "0"),
      ("Connection", "keep-alive")] "")

  let redirectBytes ← drainRequest mockClient
  mockClient.send (rawResp "200 OK"
    #[("Content-Length", "2"), ("Connection", "close")] "ok")

  match ← await resultPromise.result! with
  | Except.error e => throw (IO.userError s!"agent error: {e}")
  | Except.ok _ => pure ()

  let redirectText := String.fromUTF8! redirectBytes
  unless redirectText.startsWith "GET " do
    throw <| IO.userError
      s!"expected GET after 303, got:\n{redirectText.quote}"
  if redirectText.contains "original-body" then
    throw <| IO.userError
      s!"303 must drop body, but redirect request contained it:\n{redirectText.quote}"

-- RFC 9110 §15.4.2: "If the 301 status code is received in response to a request other
-- than GET or HEAD, the user agent MUST NOT automatically redirect the request unless it
-- can be confirmed by the user." POST→GET is the only automatic exception (prevailing
-- practice). PUT, PATCH, DELETE, etc. must not be silently redirected; the 301 is
-- returned to the caller unchanged.

#eval show IO _ from runWithTimeout "301 on PUT is not auto-followed (RFC 9110 §15.4.2)" 3000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let agent ← mkAgent mockServer

  let request ← Request.new
    |>.method .put
    |>.uri! "/v1/resource"
    |>.header! "Host" "example.com"
    |>.text "payload-x"

  let resultPromise ← sendInBackground agent request

  let _ ← drainRequest mockClient
  mockClient.send (rawResp "301 Moved Permanently"
    #[("Location", "/v2/resource"),
      ("Content-Length", "0"),
      ("Connection", "close")] "")

  match ← await resultPromise.result! with
  | Except.error e => throw (IO.userError s!"agent error: {e}")
  | Except.ok resp =>
    unless resp.line.status == .movedPermanently do
      throw <| IO.userError
        s!"expected 301 returned as-is for PUT, got {resp.line.status.toCode}"

-- 308 Permanent Redirect preserves method AND replayable body.
-- This is the distinguishing behavior vs. 301: with a replayable full body the
-- bytes must be sent again on the redirected request.

#eval show IO _ from runWithTimeout "308 Permanent Redirect replays body for PUT" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let agent ← mkAgent mockServer

  let request ← Request.new
    |>.method .put
    |>.uri! "/v1/resource"
    |>.header! "Host" "example.com"
    |>.text "replay-me"

  let resultPromise ← sendInBackground agent request

  -- First request must contain the original body.
  let mut firstBytes := ByteArray.empty
  repeat
    let some chunk ← mockClient.recv?
      | throw (IO.userError "connection closed before first body fully received")
    firstBytes := firstBytes ++ chunk
    let t := String.fromUTF8! firstBytes
    if t.endsWith "replay-me" || t.endsWith "0\r\n\r\n" then break
  mockClient.send (rawResp "308 Permanent Redirect"
    #[("Location", "/v2/resource"),
      ("Content-Length", "0"),
      ("Connection", "keep-alive")] "")

  -- Second request must contain the body again.
  let mut redirectBytes := ByteArray.empty
  repeat
    let some chunk ← mockClient.recv?
      | throw (IO.userError "connection closed before redirect body fully received")
    redirectBytes := redirectBytes ++ chunk
    let t := String.fromUTF8! redirectBytes
    if t.endsWith "replay-me" || t.endsWith "0\r\n\r\n" then break
  mockClient.send (rawResp "200 OK"
    #[("Content-Length", "2"), ("Connection", "close")] "ok")

  match ← await resultPromise.result! with
  | Except.error e => throw (IO.userError s!"agent error: {e}")
  | Except.ok _ => pure ()

  let redirectText := String.fromUTF8! redirectBytes
  unless redirectText.startsWith "PUT " do
    throw <| IO.userError s!"308 must preserve PUT:\n{redirectText.quote}"
  unless redirectText.contains "replay-me" do
    throw <| IO.userError
      s!"308 with replayable body must retransmit payload, redirect request:\n{redirectText.quote}"

-- ============================================================
-- Section 2 — Cross-origin header scrubbing
-- ============================================================

-- Proxy-Authorization must be stripped alongside Authorization on cross-origin redirects.

-- Setup: two mocks — the agent redirects from http://example.com:443 to
-- https://example.com:443 (scheme change) and opens the follow-up on a fresh
-- connection via the `connectTo` factory. The second mock carries the redirected
-- request and lets us inspect the headers the agent actually sent.
#eval show IO _ from runWithTimeout "cross-origin strips Proxy-Authorization" 4000 <| Async.block do
  let (mockClient1, mockServer1) ← Mock.new
  let (mockClient2, mockServer2) ← Mock.new
  let connection1 ← Client.Connection.new mockServer1 (config := {})
  let some domain := URI.DomainName.ofString? "example.com"
    | throw (IO.userError "DomainName parse failed")
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
    |>.header! "Proxy-Authorization" "Basic c2VjcmV0OnNlY3JldA=="
    |>.empty

  let resultPromise ← sendInBackground agent request

  -- First exchange on mock 1.
  let _ ← drainRequest mockClient1
  mockClient1.send (rawResp "302 Found"
    #[("Location", "https://example.com:443/after"),
      ("Content-Length", "0"),
      ("Connection", "close")] "")

  -- Second exchange (redirected request) on mock 2.
  let redirectBytes ← drainRequest mockClient2
  mockClient2.send (rawResp "200 OK"
    #[("Content-Length", "2"), ("Connection", "close")] "ok")

  match ← await resultPromise.result! with
  | Except.error e => throw (IO.userError s!"agent error: {e}")
  | Except.ok _ => pure ()

  let redirectText := String.fromUTF8! redirectBytes
  if redirectText.contains "Proxy-Authorization:" then
    throw <| IO.userError
      s!"Proxy-Authorization must be stripped on cross-origin redirect:\n{redirectText.quote}"

-- Cookie header set explicitly on the request must be stripped on cross-origin redirects.
-- (Jar cookies are per-host anyway; this tests the explicit Cookie header path.)

#eval show IO _ from runWithTimeout "cross-origin strips explicit Cookie header" 4000 <| Async.block do
  let (mockClient1, mockServer1) ← Mock.new
  let (mockClient2, mockServer2) ← Mock.new
  let connection1 ← Client.Connection.new mockServer1 (config := {})
  let some domain := URI.DomainName.ofString? "example.com"
    | throw (IO.userError "DomainName parse failed")
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
    |>.header! "Cookie" "session=abc123"
    |>.empty

  let resultPromise ← sendInBackground agent request

  -- First exchange on mock 1.
  let _ ← drainRequest mockClient1
  mockClient1.send (rawResp "302 Found"
    #[("Location", "https://example.com:443/after"),
      ("Content-Length", "0"),
      ("Connection", "close")] "")

  -- Second exchange on mock 2.
  let redirectBytes ← drainRequest mockClient2
  mockClient2.send (rawResp "200 OK"
    #[("Content-Length", "2"), ("Connection", "close")] "ok")

  match ← await resultPromise.result! with
  | Except.error e => throw (IO.userError s!"agent error: {e}")
  | Except.ok _ => pure ()

  let redirectText := String.fromUTF8! redirectBytes
  if redirectText.contains "session=abc123" then
    throw <| IO.userError
      s!"explicit Cookie must be stripped on cross-origin redirect:\n{redirectText.quote}"

-- ============================================================
-- Section 3 — Redirect policy
-- ============================================================

-- With maxRedirects = 0 the agent must return the 3xx response as-is.

#eval show IO _ from runWithTimeout "maxRedirects=0 returns 302 unfollowed" 3000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let agent ← mkAgent mockServer (config := { maxRedirects := 0 })

  let request ← Request.new
    |>.method .get
    |>.uri! "/"
    |>.header! "Host" "example.com"
    |>.empty

  let resultPromise ← sendInBackground agent request

  let _ ← mockClient.recv?
  mockClient.send (rawResp "302 Found"
    #[("Location", "/elsewhere"),
      ("Content-Length", "0")] "")

  -- A second recv must not occur. Run it in the background as a safety net.
  background do
    let _ ← mockClient.recv?
    pure ()

  match ← await resultPromise.result! with
  | Except.error e => throw (IO.userError s!"agent error: {e}")
  | Except.ok resp =>
    unless resp.line.status == .found do
      throw <| IO.userError
        s!"expected 302 returned unfollowed, got {resp.line.status.toCode}"

-- A 3xx response without a Location header must be returned as the final response.

#eval show IO _ from runWithTimeout "302 without Location returned as-is" 3000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let agent ← mkAgent mockServer

  let request ← Request.new
    |>.method .get
    |>.uri! "/"
    |>.header! "Host" "example.com"
    |>.empty

  let resultPromise ← sendInBackground agent request

  let _ ← mockClient.recv?
  mockClient.send (rawResp "302 Found"
    #[("Content-Length", "0"), ("Connection", "close")] "")

  match ← await resultPromise.result! with
  | Except.error e => throw (IO.userError s!"agent error: {e}")
  | Except.ok resp =>
    unless resp.line.status == .found do
      throw <| IO.userError
        s!"expected 302 (no Location) returned as-is, got {resp.line.status.toCode}"

-- A same-origin redirect loop (A → /a → /a → /a) must be broken.
-- The agent records each (host, port, uri) tuple in its history and stops when
-- it would revisit a tuple it already served in the current chain.

#eval show IO _ from runWithTimeout "redirect cycle detection stops and returns last 3xx" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let agent ← mkAgent mockServer

  let request ← Request.new
    |>.method .get
    |>.uri! "/start"
    |>.header! "Host" "example.com"
    |>.empty

  let resultPromise ← sendInBackground agent request

  -- /start → /cycle → /start (cycle).
  let _ ← drainRequest mockClient
  mockClient.send (rawResp "302 Found"
    #[("Location", "/cycle"),
      ("Content-Length", "0"),
      ("Connection", "keep-alive")] "")

  let _ ← drainRequest mockClient
  mockClient.send (rawResp "302 Found"
    #[("Location", "/start"),
      ("Content-Length", "0"),
      ("Connection", "keep-alive")] "")

  -- Cycle detected: no further requests.
  background do
    let _ ← mockClient.recv?
    pure ()

  match ← await resultPromise.result! with
  | Except.error e => throw (IO.userError s!"agent error: {e}")
  | Except.ok resp =>
    unless resp.line.status == .found do
      throw <| IO.userError
        s!"expected 302 (cycle stop), got {resp.line.status.toCode}"

-- Cycle that passes through a cross-origin hop before self-looping. The redirected request lands on
-- the new origin in absolute-form, then the origin redirects to itself in origin-form. Cycle
-- detection must normalize both forms to the same key, otherwise the self-loop is missed and the
-- agent keeps requesting the same target until `maxRedirects` (or, here, until it blocks waiting for
-- a response that never comes and the test times out).
#eval show IO _ from runWithTimeout "cross-origin then same-origin self-redirect is detected as a cycle" 4000 <| Async.block do
  let (mockClient1, mockServer1) ← Mock.new
  let (mockClient2, mockServer2) ← Mock.new
  let connection1 ← Client.Connection.new mockServer1 (config := {})
  let some domain := URI.DomainName.ofString? "example.com"
    | throw (IO.userError "DomainName parse failed")
  let agent : Client.Agent := {
    connection := connection1
    origin := { scheme := URI.Scheme.ofString! "http", host := .name domain, port := 80 }
    crossOrigin := .follow fun _ => do
      return .ok (← Client.Connection.new mockServer2 (config := {}))
  }

  let request ← Request.new
    |>.method .get
    |>.uri! "/start"
    |>.header! "Host" "example.com"
    |>.empty

  let resultPromise ← sendInBackground agent request

  -- Hop 1 on origin A: redirect cross-origin to B in absolute-form.
  let _ ← drainRequest mockClient1
  mockClient1.send (rawResp "302 Found"
    #[("Location", "http://other.com/loop"),
      ("Content-Length", "0"),
      ("Connection", "close")] "")

  -- Hop 2 on origin B: redirect to itself in origin-form. The agent must stop here.
  let _ ← drainRequest mockClient2
  mockClient2.send (rawResp "302 Found"
    #[("Location", "/loop"),
      ("Content-Length", "0"),
      ("Connection", "keep-alive")] "")

  -- If the cycle were missed, the agent would send a second request to B; drain it so the test fails
  -- with a clear message instead of hanging.
  background do
    let _ ← mockClient2.recv?
    pure ()

  match ← await resultPromise.result! with
  | Except.error e => throw (IO.userError s!"agent error: {e}")
  | Except.ok resp =>
    unless resp.line.status == .found do
      throw <| IO.userError
        s!"expected 302 (cross-origin→same-origin cycle stop), got {resp.line.status.toCode}"

-- ============================================================
-- Section 9 — 301/302 non-POST methods (RFC 9110 §15.4)
-- ============================================================
-- RFC 9110 §15.4.2-3: "MUST NOT automatically redirect the request unless it can be
-- confirmed by the user" for methods other than GET/HEAD (POST→GET is the only automatic
-- exception). HEAD on 301/302 IS auto-followed (it is safe). PATCH is NOT auto-followed.

#eval show IO _ from runWithTimeout "301 preserves HEAD method" 3000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let agent ← mkAgent mockServer

  let req ← Request.new |>.method .head |>.uri! "/old"
    |>.header! "Host" "example.com" |>.empty
  let p ← sendInBackground agent req

  let _ ← drainRequest mockClient
  mockClient.send (rawResp "301 Moved Permanently"
    #[("Location", "/new"),
      ("Content-Length", "0"),
      ("Connection", "keep-alive")] "")

  let redirectBytes ← drainRequest mockClient
  mockClient.send (rawResp "200 OK"
    #[("Content-Length", "0"), ("Connection", "close")] "")

  match ← await p.result! with
  | Except.error e => throw (IO.userError s!"agent error: {e}")
  | Except.ok _ => pure ()

  let redirectText := String.fromUTF8! redirectBytes
  unless redirectText.startsWith "HEAD " do
    throw <| IO.userError s!"301 must preserve HEAD:\n{redirectText.quote}"

-- RFC 9110 §15.4.3: same MUST NOT rule for 302. PATCH is not GET/HEAD/POST, so 302
-- on PATCH is returned to the caller as-is without sending a second request.

#eval show IO _ from runWithTimeout "302 on PATCH is not auto-followed (RFC 9110 §15.4.3)" 3000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let agent ← mkAgent mockServer

  let req ← Request.new |>.method .patch |>.uri! "/res"
    |>.header! "Host" "example.com" |>.text "patch-body"
  let p ← sendInBackground agent req

  let _ ← drainRequest mockClient
  mockClient.send (rawResp "302 Found"
    #[("Location", "/res-new"),
      ("Content-Length", "0"),
      ("Connection", "close")] "")

  match ← await p.result! with
  | Except.error e => throw (IO.userError s!"agent error: {e}")
  | Except.ok resp =>
    unless resp.line.status == .found do
      throw <| IO.userError
        s!"expected 302 returned as-is for PATCH, got {resp.line.status.toCode}"

-- ============================================================
-- Section 10 — Relative Location preserves scheme and host
-- ============================================================
-- A `Location: /path` (relative) must not change the request's scheme, host or
-- port. The earlier redirect tests implicitly rely on this but none asserts it.

#eval show IO _ from runWithTimeout "relative Location preserves host and scheme" 3000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let agent ← mkAgent mockServer

  let req ← Request.new |>.method .get |>.uri! "/old"
    |>.header! "Host" "example.com" |>.empty
  let p ← sendInBackground agent req

  let _ ← drainRequest mockClient
  mockClient.send (rawResp "302 Found"
    #[("Location", "/new"),
      ("Content-Length", "0"),
      ("Connection", "keep-alive")] "")

  let redirectBytes ← drainRequest mockClient
  mockClient.send (rawResp "200 OK"
    #[("Content-Length", "0"), ("Connection", "close")] "")

  match ← await p.result! with
  | Except.error e => throw (IO.userError s!"agent error: {e}")
  | Except.ok _ => pure ()

  let redirectText := String.fromUTF8! redirectBytes
  -- Host header must still reference example.com.
  unless redirectText.contains "Host: example.com" do
    throw <| IO.userError
      s!"relative redirect must preserve Host header:\n{redirectText.quote}"
  -- And the target must be /new (origin-form, not absolute-form).
  unless redirectText.startsWith "GET /new" do
    throw <| IO.userError
      s!"expected GET /new, got:\n{redirectText.quote}"
