module

import Std.Http.Test.Helpers

/-! HTTP client redirect rewriting, security, policy, and target-resolution edge cases. -/

open Std.Async
open Std Http Internal
open Test.ClientHelpers

-- ============================================================
-- Section 1 — Redirect method/body rewrites (RFC 9110 §15.4)
-- ============================================================

-- 303 See Other: any method → GET, body dropped.
-- The existing tests cover 302 POST→GET; this one covers the non-POST path.

#eval show IO _ from runWithTimeout "303 See Other converts PUT to GET and drops body" 3000 <|
  Async.block do
  let (mockClient, mockServer) ← Mock.new
  let client ← mkClient mockServer

  let request ← Request.new
    |>.method .put
    |>.uri! "/upload"
    |>.header! "Host" "example.com"
    |>.text "original-body"

  let resultPromise ← sendInBackground client request

  let _ ← drainRequest mockClient
  mockClient.send (rawResp "303 See Other"
    #[("Location", "/after-put"),
      ("Content-Length", "0"),
      ("Connection", "keep-alive")] "")

  let redirectBytes ← drainRequest mockClient
  mockClient.send (rawResp "200 OK"
    #[("Content-Length", "2"), ("Connection", "close")] "ok")

  match ← await resultPromise.result! with
  | Except.error e => throw (IO.userError s!"client error: {e}")
  | Except.ok _ => pure ()

  let redirectText := String.fromUTF8! redirectBytes
  unless redirectText.startsWith "GET " do
    throw <| IO.userError
      s!"expected GET after 303, got:\n{redirectText.quote}"
  if redirectText.contains "original-body" then
    throw <| IO.userError
      s!"303 must drop body, but redirect request contained it:\n{redirectText.quote}"

-- RFC 9110 §15.4.2: "If the 301 status code is received in response to a request other
-- than GET or HEAD, the user client MUST NOT automatically redirect the request unless it
-- can be confirmed by the user." POST→GET is the only automatic exception (prevailing
-- practice). PUT, PATCH, DELETE, etc. must not be silently redirected; the 301 is
-- returned to the caller unchanged.

#eval show IO _ from runWithTimeout "301 on PUT is not auto-followed (RFC 9110 §15.4.2)" 3000 <|
  Async.block do
  let (mockClient, mockServer) ← Mock.new
  let client ← mkClient mockServer

  let request ← Request.new
    |>.method .put
    |>.uri! "/v1/resource"
    |>.header! "Host" "example.com"
    |>.text "payload-x"

  let resultPromise ← sendInBackground client request

  -- Keep-alive, so the method rule is the only thing that can stop the follow: a 3xx that ends the
  -- connection is handed back unfollowed on its own, and the test would pass with the rule gone.
  let _ ← drainRequest mockClient
  mockClient.send (rawResp "301 Moved Permanently"
    #[("Location", "/v2/resource"),
      ("Content-Length", "0"),
      ("Connection", "keep-alive")] "")

  let followed ← IO.mkRef (none : Option ByteArray)
  background do
    followed.set (← mockClient.recv?)

  match ← await resultPromise.result! with
  | Except.error e => throw (IO.userError s!"client error: {e}")
  | Except.ok resp =>
    resp.body.close
    unless resp.line.status == .movedPermanently do
      throw <| IO.userError
        s!"expected 301 returned as-is for PUT, got {resp.line.status.toCode}"

  IO.sleep 100
  if let some bytes ← followed.get then
    throw <| IO.userError
      s!"a 301 on PUT was auto-followed:\n{(String.fromUTF8! bytes).quote}"

-- 308 Permanent Redirect preserves method AND replayable body.
-- This is the distinguishing behavior vs. 301: with a replayable full body the
-- bytes must be sent again on the redirected request.

#eval show IO _ from runWithTimeout "308 Permanent Redirect replays body for PUT" 4000 <|
  Async.block do
  let (mockClient, mockServer) ← Mock.new
  let client ← mkClient mockServer

  let request ← Request.new
    |>.method .put
    |>.uri! "/v1/resource"
    |>.header! "Host" "example.com"
    |>.text "replay-me"

  let resultPromise ← sendInBackground client request

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
  | Except.error e => throw (IO.userError s!"client error: {e}")
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

-- Setup: two mocks — the client redirects from http://example.com:443 to
-- https://example.com:443 (scheme change) and opens the follow-up on a fresh
-- connection via the `connectTo` factory. The second mock carries the redirected
-- request and lets us inspect the headers the client actually sent.
#eval show IO _ from runWithTimeout "cross-origin strips Proxy-Authorization" 4000 <| Async.block do
  let (mockClient1, mockServer1) ← Mock.new
  let (mockClient2, mockServer2) ← Mock.new
  let (client, _) ← mkFollowingClient #[mockServer1, mockServer2] (port := 443)

  let request ← Request.new
    |>.method .get
    |>.uri! "/"
    |>.header! "Host" "example.com:443"
    |>.header! "Proxy-Authorization" "Basic c2VjcmV0OnNlY3JldA=="
    |>.empty

  let resultPromise ← sendInBackground client request

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
  | Except.error e => throw (IO.userError s!"client error: {e}")
  | Except.ok _ => pure ()

  let redirectText := String.fromUTF8! redirectBytes
  if redirectText.contains "Proxy-Authorization:" then
    throw <| IO.userError
      s!"Proxy-Authorization must be stripped on cross-origin redirect:\n{redirectText.quote}"

-- Cookie header set explicitly on the request must be stripped on cross-origin redirects.
-- (Jar cookies are per-host anyway; this tests the explicit Cookie header path.)

#eval show IO _ from runWithTimeout "cross-origin strips explicit Cookie header" 4000 <|
  Async.block do
  let (mockClient1, mockServer1) ← Mock.new
  let (mockClient2, mockServer2) ← Mock.new
  let (client, _) ← mkFollowingClient #[mockServer1, mockServer2] (port := 443)

  let request ← Request.new
    |>.method .get
    |>.uri! "/"
    |>.header! "Host" "example.com:443"
    |>.header! "Cookie" "session=abc123"
    |>.empty

  let resultPromise ← sendInBackground client request

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
  | Except.error e => throw (IO.userError s!"client error: {e}")
  | Except.ok _ => pure ()

  let redirectText := String.fromUTF8! redirectBytes
  if redirectText.contains "session=abc123" then
    throw <| IO.userError
      s!"explicit Cookie must be stripped on cross-origin redirect:\n{redirectText.quote}"

-- ============================================================
-- Section 3 — Redirect policy
-- ============================================================

-- With maxRedirects = 0 the client must return the 3xx response as-is.

#eval show IO _ from runWithTimeout "maxRedirects=0 returns 302 unfollowed" 3000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let client ← mkClient mockServer (config := { maxRedirects := 0 })

  let request ← Request.new
    |>.method .get
    |>.uri! "/"
    |>.header! "Host" "example.com"
    |>.empty

  let resultPromise ← sendInBackground client request

  -- Drain the whole request: a partial read would leave its tail to be mistaken below for a
  -- redirect hop that was never sent.
  let _ ← drainRequest mockClient
  mockClient.send (rawResp "302 Found"
    #[("Location", "/elsewhere"),
      ("Content-Length", "0")] "")

  -- A second request must never reach the wire; draining in the background keeps the client from
  -- blocking if it wrongly sends one, so the assertion below reports it instead of timing out.
  let followed ← IO.mkRef (none : Option ByteArray)
  background do
    followed.set (← mockClient.recv?)

  match ← await resultPromise.result! with
  | Except.error e => throw (IO.userError s!"client error: {e}")
  | Except.ok resp =>
    resp.body.close
    unless resp.line.status == .found do
      throw <| IO.userError
        s!"expected 302 returned unfollowed, got {resp.line.status.toCode}"

  IO.sleep 100
  if let some bytes ← followed.get then
    throw <| IO.userError
      s!"maxRedirects := 0 still followed the redirect:\n{(String.fromUTF8! bytes).quote}"

-- A 3xx response without a Location header must be returned as the final response.

#eval show IO _ from runWithTimeout "302 without Location returned as-is" 3000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let client ← mkClient mockServer

  let request ← Request.new
    |>.method .get
    |>.uri! "/"
    |>.header! "Host" "example.com"
    |>.empty

  let resultPromise ← sendInBackground client request

  let _ ← drainRequest mockClient
  mockClient.send (rawResp "302 Found"
    #[("Content-Length", "0"), ("Connection", "close")] "")

  match ← await resultPromise.result! with
  | Except.error e => throw (IO.userError s!"client error: {e}")
  | Except.ok resp =>
    unless resp.line.status == .found do
      throw <| IO.userError
        s!"expected 302 (no Location) returned as-is, got {resp.line.status.toCode}"

-- A same-origin redirect loop (A → /a → /a → /a) must be broken.
-- The client records each (host, port, uri) tuple in its history and stops when
-- it would revisit a tuple it already served in the current chain.

#eval show IO _ from runWithTimeout "redirect cycle detection stops and returns last 3xx" 4000 <|
  Async.block do
  let (mockClient, mockServer) ← Mock.new
  let client ← mkClient mockServer

  let request ← Request.new
    |>.method .get
    |>.uri! "/start"
    |>.header! "Host" "example.com"
    |>.empty

  let resultPromise ← sendInBackground client request

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

  -- Cycle detected: no further requests. A missed cycle is both drained *and answered* here, so
  -- the client completes and the assertions below name the failure — without the reply the client
  -- blocks on a response that never comes and the test dies on the wall clock instead.
  let looped ← IO.mkRef (none : Option ByteArray)
  background do
    if let some bytes ← mockClient.recv? then
      looped.set (some bytes)
      mockClient.send (rawResp "200 OK" #[("Content-Length", "0"), ("Connection", "close")] "")

  match ← await resultPromise.result! with
  | Except.error e => throw (IO.userError s!"client error: {e}")
  | Except.ok resp =>
    resp.body.close
    unless resp.line.status == .found do
      throw <| IO.userError
        s!"expected 302 (cycle stop), got {resp.line.status.toCode}"

  IO.sleep 100
  if let some bytes ← looped.get then
    throw <| IO.userError
      s!"the redirect cycle was not detected; a third hop went out:\n{(String.fromUTF8! bytes).quote}"

-- Cycle that passes through a cross-origin hop before self-looping. The redirected request lands on
-- the new origin in absolute-form, then the origin redirects to itself in origin-form. Cycle
-- detection must normalize both forms to the same key, otherwise the self-loop is missed and the
-- client keeps requesting the same target until `maxRedirects` (or, here, until it blocks waiting
-- a response that never comes and the test times out).
#eval show IO _ from
  runWithTimeout "cross-origin then same-origin self-redirect is detected as a cycle" 4000 <|
  Async.block do
  let (mockClient1, mockServer1) ← Mock.new
  let (mockClient2, mockServer2) ← Mock.new
  let (client, _) ← mkFollowingClient #[mockServer1, mockServer2]

  let request ← Request.new
    |>.method .get
    |>.uri! "/start"
    |>.header! "Host" "example.com"
    |>.empty

  let resultPromise ← sendInBackground client request

  -- Hop 1 on origin A: redirect cross-origin to B in absolute-form.
  let _ ← drainRequest mockClient1
  mockClient1.send (rawResp "302 Found"
    #[("Location", "http://other.com/loop"),
      ("Content-Length", "0"),
      ("Connection", "close")] "")

  -- Hop 2 on origin B: redirect to itself in origin-form. The client must stop here.
  let _ ← drainRequest mockClient2
  mockClient2.send (rawResp "302 Found"
    #[("Location", "/loop"),
      ("Content-Length", "0"),
      ("Connection", "keep-alive")] "")

  -- If the cycle were missed, the client would send a second request to B; drain *and answer* it so
  -- the test fails with a clear message instead of hanging.
  let looped ← IO.mkRef (none : Option ByteArray)
  background do
    if let some bytes ← mockClient2.recv? then
      looped.set (some bytes)
      mockClient2.send (rawResp "200 OK" #[("Content-Length", "0"), ("Connection", "close")] "")

  match ← await resultPromise.result! with
  | Except.error e => throw (IO.userError s!"client error: {e}")
  | Except.ok resp =>
    resp.body.close
    unless resp.line.status == .found do
      throw <| IO.userError
        s!"expected 302 (cross-origin→same-origin cycle stop), got {resp.line.status.toCode}"

  IO.sleep 100
  if let some bytes ← looped.get then
    throw <| IO.userError
      s!"the cross-origin self-loop was not detected:\n{(String.fromUTF8! bytes).quote}"

-- ============================================================
-- Section 9 — 301/302 non-POST methods (RFC 9110 §15.4)
-- ============================================================
-- RFC 9110 §15.4.2-3: "MUST NOT automatically redirect the request unless it can be
-- confirmed by the user" for methods other than GET/HEAD (POST→GET is the only automatic
-- exception). HEAD on 301/302 IS auto-followed (it is safe). PATCH is NOT auto-followed.

#eval show IO _ from runWithTimeout "301 preserves HEAD method" 3000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let client ← mkClient mockServer

  let req ← Request.new |>.method .head |>.uri! "/old"
    |>.header! "Host" "example.com" |>.empty
  let p ← sendInBackground client req

  let _ ← drainRequest mockClient
  mockClient.send (rawResp "301 Moved Permanently"
    #[("Location", "/new"),
      ("Content-Length", "0"),
      ("Connection", "keep-alive")] "")

  let redirectBytes ← drainRequest mockClient
  mockClient.send (rawResp "200 OK"
    #[("Content-Length", "0"), ("Connection", "close")] "")

  match ← await p.result! with
  | Except.error e => throw (IO.userError s!"client error: {e}")
  | Except.ok _ => pure ()

  let redirectText := String.fromUTF8! redirectBytes
  unless redirectText.startsWith "HEAD " do
    throw <| IO.userError s!"301 must preserve HEAD:\n{redirectText.quote}"

-- RFC 9110 §15.4.3: same MUST NOT rule for 302. PATCH is not GET/HEAD/POST, so 302
-- on PATCH is returned to the caller as-is without sending a second request.

#eval show IO _ from runWithTimeout "302 on PATCH is not auto-followed (RFC 9110 §15.4.3)" 3000 <|
  Async.block do
  let (mockClient, mockServer) ← Mock.new
  let client ← mkClient mockServer

  let req ← Request.new |>.method .patch |>.uri! "/res"
    |>.header! "Host" "example.com" |>.text "patch-body"
  let p ← sendInBackground client req

  -- Keep-alive for the same reason as the 301/PUT case above: only the method rule may stop this.
  let _ ← drainRequest mockClient
  mockClient.send (rawResp "302 Found"
    #[("Location", "/res-new"),
      ("Content-Length", "0"),
      ("Connection", "keep-alive")] "")

  let followed ← IO.mkRef (none : Option ByteArray)
  background do
    followed.set (← mockClient.recv?)

  match ← await p.result! with
  | Except.error e => throw (IO.userError s!"client error: {e}")
  | Except.ok resp =>
    resp.body.close
    unless resp.line.status == .found do
      throw <| IO.userError
        s!"expected 302 returned as-is for PATCH, got {resp.line.status.toCode}"

  IO.sleep 100
  if let some bytes ← followed.get then
    throw <| IO.userError
      s!"a 302 on PATCH was auto-followed:\n{(String.fromUTF8! bytes).quote}"

-- ============================================================
-- Section 10 — Relative Location preserves scheme and host
-- ============================================================
-- A `Location: /path` (relative) must not change the request's scheme, host or
-- port. The earlier redirect tests implicitly rely on this but none asserts it.

#eval show IO _ from runWithTimeout "relative Location preserves host and scheme" 3000 <|
  Async.block do
  let (mockClient, mockServer) ← Mock.new
  let client ← mkClient mockServer

  let req ← Request.new |>.method .get |>.uri! "/old"
    |>.header! "Host" "example.com" |>.empty
  let p ← sendInBackground client req

  let _ ← drainRequest mockClient
  mockClient.send (rawResp "302 Found"
    #[("Location", "/new"),
      ("Content-Length", "0"),
      ("Connection", "keep-alive")] "")

  let redirectBytes ← drainRequest mockClient
  mockClient.send (rawResp "200 OK"
    #[("Content-Length", "0"), ("Connection", "close")] "")

  match ← await p.result! with
  | Except.error e => throw (IO.userError s!"client error: {e}")
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

-- ============================================================
-- Section 11 — Per-request `onlySafeRedirects` override
-- ============================================================
-- `RequestOverrides.onlySafeRedirects` gates automatic following for unsafe methods
-- on a single request without changing the client-wide `Config`. The two tests below
-- send the identical POST/302 exchange and differ only in the override.

-- Control: with the default policy (`onlySafeRedirects := false`) a 302 on POST is
-- followed with the RFC 9110 §15.4.4 POST→GET downgrade.

#eval show IO _ from runWithTimeout "302 on POST is followed under the default policy" 3000 <|
  Async.block do
  let (mockClient, mockServer) ← Mock.new
  let client ← mkClient mockServer

  let req ← Request.new |>.method .post |>.uri! "/submit"
    |>.header! "Host" "example.com" |>.text "payload"
  let p ← sendInBackground client req

  let _ ← drainRequest mockClient
  mockClient.send (rawResp "302 Found"
    #[("Location", "/done"),
      ("Content-Length", "0"),
      ("Connection", "keep-alive")] "")

  let redirectBytes ← drainRequest mockClient
  mockClient.send (rawResp "200 OK"
    #[("Content-Length", "0"), ("Connection", "close")] "")

  match ← await p.result! with
  | Except.error e => throw (IO.userError s!"client error: {e}")
  | Except.ok resp =>
    unless resp.line.status == .ok do
      throw <| IO.userError s!"expected the redirect to be followed, got {resp.line.status.toCode}"

  let redirectText := String.fromUTF8! redirectBytes
  unless redirectText.startsWith "GET /done" do
    throw <| IO.userError s!"expected GET /done after POST downgrade, got:\n{redirectText.quote}"

-- With `onlySafeRedirects := some true` the same exchange stops at the 302: POST is not
-- a safe method, so the response is handed to the caller and no second request is sent.

#eval show IO _ from runWithTimeout "onlySafeRedirects override stops a 302 on POST" 3000 <|
  Async.block do
  let (mockClient, mockServer) ← Mock.new
  let client ← mkClient mockServer

  let req ← Request.new |>.method .post |>.uri! "/submit"
    |>.header! "Host" "example.com" |>.text "payload"
  let p ← sendInBackground client req { onlySafeRedirects := some true }

  -- Keep-alive: the control test above sends the identical exchange, so the override must be the
  -- only difference between following and not. A closing 3xx would stop the chain by itself.
  let _ ← drainRequest mockClient
  mockClient.send (rawResp "302 Found"
    #[("Location", "/done"),
      ("Content-Length", "0"),
      ("Connection", "keep-alive")] "")

  let followed ← IO.mkRef (none : Option ByteArray)
  background do
    followed.set (← mockClient.recv?)

  match ← await p.result! with
  | Except.error e => throw (IO.userError s!"client error: {e}")
  | Except.ok resp =>
    resp.body.close
    unless resp.line.status == .found do
      throw <| IO.userError
        s!"expected the 302 returned as-is under onlySafeRedirects, got {resp.line.status.toCode}"

  IO.sleep 100
  if let some bytes ← followed.get then
    throw <| IO.userError
      s!"onlySafeRedirects did not stop the POST redirect:\n{(String.fromUTF8! bytes).quote}"

-- ============================================================
-- Section 8 — Redirects across a connection the response ended
-- ============================================================

-- A same-origin hop used to reuse the connection the 3xx arrived on unconditionally. When the
-- response says `Connection: close` that connection is already going away, so the next hop could
-- not be written and the caller saw a transport error instead of the redirect target. A `.follow`
-- policy has to be consulted for a same-origin hop too, not only for a cross-origin one.

#eval show IO _ from
  runWithTimeout "same-origin redirect is followed when the 3xx says Connection: close" 5000 <|
  Async.block do
  let (mockClient1, mockServer1) ← Mock.new
  let (mockClient2, mockServer2) ← Mock.new
  let (client, dialled) ← mkFollowingClient #[mockServer1, mockServer2]

  let req ← Request.new |>.method .get |>.uri! "/start"
    |>.header! "Host" "example.com" |>.empty
  let p ← sendInBackground client req

  let _ ← drainRequest mockClient1
  mockClient1.send (rawResp "302 Found"
    #[("Location", "/landing"), ("Content-Length", "0"), ("Connection", "close")] "")
  mockClient1.close

  -- The redirected hop must land on a fresh connection to the same origin.
  let redirectBytes ← drainRequest mockClient2
  mockClient2.send (rawResp "200 OK" #[("Content-Length", "7"), ("Connection", "close")] "landed!")

  match ← await p.result! with
  | Except.error e =>
    throw <| IO.userError
      s!"redirect on a closing connection failed instead of reconnecting: {e}"
  | Except.ok resp =>
    let body ← resp.body.readAll (α := String)
    unless body == "landed!" do
      throw <| IO.userError s!"expected redirect target body 'landed!', got {body.quote}"

  let redirectText := String.fromUTF8! redirectBytes
  unless redirectText.startsWith "GET /landing" do
    throw <| IO.userError s!"unexpected redirected request:\n{redirectText.quote}"
  unless (← dialled.get).map (·.hostHeader) == #["example.com"] do
    throw <| IO.userError
      s!"expected one fresh connection to example.com, dialled {(← dialled.get).map (·.hostHeader)}"

-- The same situation reached without an explicit `Connection: close`: a 3xx whose body is
-- delimited by connection close (no Content-Length, no Transfer-Encoding) ends the connection too.

#eval show IO _ from
  runWithTimeout "same-origin redirect is followed when the 3xx body is close-delimited" 5000 <|
  Async.block do
  let (mockClient1, mockServer1) ← Mock.new
  let (mockClient2, mockServer2) ← Mock.new
  let (client, _) ← mkFollowingClient #[mockServer1, mockServer2]

  let req ← Request.new |>.method .get |>.uri! "/start"
    |>.header! "Host" "example.com" |>.empty
  let p ← sendInBackground client req

  let _ ← drainRequest mockClient1
  mockClient1.send "HTTP/1.1 302 Found\r\nLocation: /landing\r\n\r\nmoved".toUTF8
  mockClient1.close

  let redirectBytes ← drainRequest mockClient2
  mockClient2.send (rawResp "200 OK" #[("Content-Length", "7"), ("Connection", "close")] "landed!")

  match ← await p.result! with
  | Except.error e =>
    throw <| IO.userError s!"close-delimited redirect failed instead of reconnecting: {e}"
  | Except.ok resp =>
    let body ← resp.body.readAll (α := String)
    unless body == "landed!" do
      throw <| IO.userError s!"expected redirect target body 'landed!', got {body.quote}"

  let redirectText := String.fromUTF8! redirectBytes
  unless redirectText.startsWith "GET /landing" do
    throw <| IO.userError s!"unexpected redirected request:\n{redirectText.quote}"

-- `RedirectPlan.rewriteHostHeader` only rewrites a `Host` that is already there; supplying one is
-- documented as the caller's job, and the caller here is the `Agent`, which knows both origins.
-- A request sent without `Host` must not reach a *different* host with no `Host` at all.

#eval show IO _ from
  runWithTimeout "cross-origin redirect supplies Host for the new origin" 5000 <|
  Async.block do
  let (mockClient1, mockServer1) ← Mock.new
  let (mockClient2, mockServer2) ← Mock.new
  let (client, dialled) ← mkFollowingClient #[mockServer1, mockServer2]

  let req ← Request.new |>.method .get |>.uri! "/start" |>.empty
  let p ← sendInBackground client req

  let _ ← drainRequest mockClient1
  mockClient1.send (rawResp "302 Found"
    #[("Location", "http://other.example/landing"), ("Content-Length", "0"),
      ("Connection", "keep-alive")] "")

  let redirectBytes ← drainRequest mockClient2
  mockClient2.send (rawResp "200 OK" #[("Content-Length", "2"), ("Connection", "close")] "ok")

  match ← await p.result! with
  | Except.error e => throw (IO.userError s!"cross-origin redirect failed: {e}")
  | Except.ok resp => resp.body.close

  let redirectText := String.fromUTF8! redirectBytes
  unless redirectText.contains "Host: other.example" do
    throw <| IO.userError
      s!"redirected request went to other.example without a Host header:\n{redirectText.quote}"
  -- The `Host` has to match the origin the hop was actually dialled at, not just be present.
  unless (← dialled.get).map (·.hostHeader) == #["other.example"] do
    throw <| IO.userError
      s!"the hop was dialled at {(← dialled.get).map (·.hostHeader)}, not other.example"

-- ============================================================
-- A connection retired for a reason the response head does not mention
-- ============================================================

-- Whether the connection carries the next hop is the connection's decision. Reading it off the
-- redirect response alone misses every client-side reason the connection is going away: the 3xx
-- below offers `keep-alive`, but `enableKeepAlive := false` made the client ask for closure, and
-- `maxRequestsPerConnection := 1` spends the connection's whole budget on the first hop. Either
-- way the hop has to continue on a freshly dialled connection rather than the retired one.

/--
Runs a same-origin redirect under `config` through a client whose connector can hand out a
second connection, and checks the hop continues from `/b` on it.
-/
private def followedRedirect (name : String) (config : Client.Config) : Async Unit := do
  let (mockClient1, mockServer1) ← Mock.new
  let (mockClient2, mockServer2) ← Mock.new
  let (client, dialled) ← mkFollowingClient #[mockServer1, mockServer2] config

  let req ← Request.new |>.method .get |>.uri! "/a"
    |>.header! "Host" "example.com" |>.empty
  let p ← sendInBackground client req

  let _ ← drainRequest mockClient1
  mockClient1.send (rawResp "302 Found"
    #[("Location", "/b"), ("Content-Length", "0"), ("Connection", "keep-alive")] "")

  -- The next hop must be the redirect target on the fresh connection, not a replay of `/a`.
  let second ← drainRequest mockClient2
  unless (String.fromUTF8! second).startsWith "GET /b" do
    throw <| IO.userError
      s!"{name}: second connection did not receive the redirect hop:\n{(String.fromUTF8! second).quote}"
  mockClient2.send (rawResp "200 OK" #[("Content-Length", "2"), ("Connection", "close")] "ok")

  match ← await p.result! with
  | Except.error e => throw <| IO.userError s!"{name}: redirect failed: {e}"
  | Except.ok resp =>
    let body ← resp.body.readAll (α := String)
    unless body == "ok" do throw <| IO.userError s!"{name}: expected 'ok', got {body.quote}"

  unless (← dialled.get).size == 1 do
    throw <| IO.userError
      s!"{name}: expected exactly one reconnect, got {(← dialled.get).size}"

#eval show IO _ from
  runWithTimeout "the client reconnects for the redirect when the old connection is retired"
    8000 <| Async.block do
  followedRedirect "enableKeepAlive := false" { enableKeepAlive := false }
  followedRedirect "maxRequestsPerConnection := 1" { maxRequestsPerConnection := 1 }
