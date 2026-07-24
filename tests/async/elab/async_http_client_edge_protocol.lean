module

import Std.Http.Test.Helpers

open Std.Async
open Std Http Internal
open Test.ClientHelpers

/-! HTTP client wire-protocol, framing, response-limit, and body-stream edge cases. -/

-- ============================================================
-- Section 4 — Expect: 100-continue
-- ============================================================

-- Happy path: server sends 100, client pumps body, server sends 200.

#eval show IO _ from runWithTimeout "Expect: 100-continue happy path sends body after 100" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let agent ← mkAgent mockServer

  let request ← Request.new
    |>.method .post
    |>.uri! "/submit"
    |>.header! "Host" "example.com"
    |>.header! "Expect" "100-continue"
    |>.text "actual-body"

  let resultPromise ← sendInBackground agent request

  -- Read the header-only request first: the client must NOT send the body yet.
  let mut headerBytes := ByteArray.empty
  repeat
    let some chunk ← mockClient.recv?
      | throw (IO.userError "connection closed before headers received")
    headerBytes := headerBytes ++ chunk
    let t := String.fromUTF8! headerBytes
    if t.contains "\r\n\r\n" then break
  let headerText := String.fromUTF8! headerBytes
  if headerText.contains "actual-body" then
    throw <| IO.userError
      s!"client sent body before 100 Continue:\n{headerText.quote}"

  -- Send 100 Continue.
  mockClient.send "HTTP/1.1 100 Continue\r\n\r\n".toUTF8

  -- Now the client should push the body. Read until we see "actual-body".
  let mut bodyBytes := headerBytes
  repeat
    let t := String.fromUTF8! bodyBytes
    if t.contains "actual-body" then break
    let some chunk ← mockClient.recv?
      | throw (IO.userError "connection closed before body received")
    bodyBytes := bodyBytes ++ chunk

  mockClient.send (rawResp "200 OK"
    #[("Content-Length", "2"), ("Connection", "close")] "ok")

  match ← await resultPromise.result! with
  | Except.error e => throw (IO.userError s!"agent error: {e}")
  | Except.ok resp =>
    unless resp.line.status.toCode == 200 do
      throw <| IO.userError s!"expected 200, got {resp.line.status.toCode}"

-- 4xx rejection: server rejects with 417 before reading body; body must not be sent.

#eval show IO _ from runWithTimeout "Expect: 100-continue 417 rejection discards body" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let agent ← mkAgent mockServer

  let request ← Request.new
    |>.method .post
    |>.uri! "/submit"
    |>.header! "Host" "example.com"
    |>.header! "Expect" "100-continue"
    |>.text "rejected-body"

  let resultPromise ← sendInBackground agent request

  -- Read header-only.
  let mut headerBytes := ByteArray.empty
  repeat
    let some chunk ← mockClient.recv?
      | throw (IO.userError "connection closed before headers received")
    headerBytes := headerBytes ++ chunk
    let t := String.fromUTF8! headerBytes
    if t.contains "\r\n\r\n" then break
  let headerText := String.fromUTF8! headerBytes
  if headerText.contains "rejected-body" then
    throw <| IO.userError
      s!"client sent body before server response:\n{headerText.quote}"

  -- Reject with 417 Expectation Failed (instead of 100). Close after.
  mockClient.send (rawResp "417 Expectation Failed"
    #[("Content-Length", "0"), ("Connection", "close")] "")

  -- Observe the wire: the rejected body must never appear.
  let leakedRef ← IO.mkRef false
  background do
    let mut acc := ByteArray.empty
    repeat
      match ← mockClient.recv? with
      | none => break
      | some c =>
        acc := acc ++ c
        if (String.fromUTF8! acc).contains "rejected-body" then
          leakedRef.set true
          break

  match ← await resultPromise.result! with
  | Except.error _ =>
    -- Error from the agent is acceptable — key check is no body leak.
    pure ()
  | Except.ok resp =>
    unless resp.line.status.toCode == 417 do
      throw <| IO.userError s!"expected 417, got {resp.line.status.toCode}"

  -- Give the drain task a brief moment to observe any stray writes.
  IO.sleep 50
  if ← leakedRef.get then
    throw (IO.userError "body was sent after 417 Expectation Failed")

-- Server bypass: no 100 is sent, the server jumps straight to a 2xx response
-- before the body has been pumped. The pending body must be discarded so the
-- connection is not stuck.

#eval show IO _ from runWithTimeout "Expect: 100-continue bypass with early 200 discards pending body" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let agent ← mkAgent mockServer

  let request ← Request.new
    |>.method .post
    |>.uri! "/submit"
    |>.header! "Host" "example.com"
    |>.header! "Expect" "100-continue"
    |>.text "unused-body"

  let resultPromise ← sendInBackground agent request

  -- Read only headers.
  let mut headerBytes := ByteArray.empty
  repeat
    let some chunk ← mockClient.recv?
      | throw (IO.userError "connection closed before headers")
    headerBytes := headerBytes ++ chunk
    let t := String.fromUTF8! headerBytes
    if t.contains "\r\n\r\n" then break

  -- Send a direct 200 (bypass 100-continue). Close the connection so the agent
  -- does not hang waiting for more responses.
  mockClient.send (rawResp "200 OK"
    #[("Content-Length", "2"), ("Connection", "close")] "ok")

  match ← await resultPromise.result! with
  | Except.error e => throw (IO.userError s!"agent error on bypass: {e}")
  | Except.ok resp =>
    unless resp.line.status.toCode == 200 do
      throw <| IO.userError s!"expected 200 on bypass, got {resp.line.status.toCode}"

-- ============================================================
-- Section 5 — Informational responses (1xx) are transparent
-- ============================================================

-- 103 Early Hints must not resolve the caller — the final response must arrive.

#eval show IO _ from runWithTimeout "103 Early Hints is transparent" 3000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let agent ← mkAgent mockServer

  let request ← Request.new
    |>.method .get
    |>.uri! "/"
    |>.header! "Host" "example.com"
    |>.empty

  let resultPromise ← sendInBackground agent request

  let _ ← mockClient.recv?
  -- 103 with a couple of hint headers, then the real 200.
  mockClient.send "HTTP/1.1 103 Early Hints\r\nLink: </style.css>; rel=preload\r\n\r\n".toUTF8
  mockClient.send (rawResp "200 OK"
    #[("Content-Length", "2"), ("Connection", "close")] "ok")

  match ← await resultPromise.result! with
  | Except.error e => throw (IO.userError s!"agent error: {e}")
  | Except.ok resp =>
    unless resp.line.status.toCode == 200 do
      throw <| IO.userError
        s!"103 must be transparent; expected 200, got {resp.line.status.toCode}"

-- Multiple consecutive 1xx responses must all be skipped before the real response.

#eval show IO _ from runWithTimeout "multiple 103 responses all skipped" 3000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let agent ← mkAgent mockServer

  let request ← Request.new
    |>.method .get
    |>.uri! "/"
    |>.header! "Host" "example.com"
    |>.empty

  let resultPromise ← sendInBackground agent request

  let _ ← mockClient.recv?
  mockClient.send "HTTP/1.1 103 Early Hints\r\nLink: </a.css>; rel=preload\r\n\r\n".toUTF8
  mockClient.send "HTTP/1.1 103 Early Hints\r\nLink: </b.css>; rel=preload\r\n\r\n".toUTF8
  mockClient.send (rawResp "200 OK"
    #[("Content-Length", "2"), ("Connection", "close")] "ok")

  match ← await resultPromise.result! with
  | Except.error e => throw (IO.userError s!"agent error: {e}")
  | Except.ok resp =>
    unless resp.line.status.toCode == 200 do
      throw <| IO.userError
        s!"expected 200 after repeated 103s, got {resp.line.status.toCode}"

-- ============================================================
-- Section 6 — Response body size limit
-- ============================================================

-- A response body longer than `maxResponseBodySize` must fail the request with an error.
-- The body must be reported via the body stream; reading it should see the error
-- bubble up through the agent.send promise.

#eval show IO _ from runWithTimeout "maxResponseBodySize exceeded errors the request" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let agent ← mkAgent mockServer (config := { maxResponseBodySize := some 4 })

  let request ← Request.new
    |>.method .get
    |>.uri! "/big"
    |>.header! "Host" "example.com"
    |>.empty

  let resultPromise ← sendInBackground agent request

  let _ ← drainRequest mockClient
  -- Advertise 16 bytes (well over the 4-byte limit) and send them all.
  mockClient.send (rawResp "200 OK"
    #[("Content-Length", "16"), ("Connection", "close")] "0123456789ABCDEF")

  match ← await resultPromise.result! with
  | Except.error _ =>
    -- Agent surfaced an error up-front — acceptable: the limit was enforced.
    pure ()
  | Except.ok resp =>
    -- Headers may resolve before the limit triggers. Reading the body must
    -- either error or stop short of the full 16 bytes.
    let got : Except String String ← try
        let s ← resp.body.readAll (α := String)
        pure (Except.ok s)
      catch e => pure (Except.error (toString e))
    match got with
    | Except.ok s =>
      if s.toUTF8.size > 4 then
        throw (IO.userError s!"response body limit not enforced; read {s.toUTF8.size} bytes")
    | Except.error _ => pure ()

-- The response-body limit is inclusive: exactly `maxResponseBodySize` bytes are accepted, while
-- the first byte beyond the limit fails the stream.
#eval show IO _ from runWithTimeout "maxResponseBodySize exact boundary is inclusive" 4000 <| Async.block do
  let (atLimitClient, atLimitServer) ← Mock.new
  let atLimitAgent ← mkAgent atLimitServer (config := { maxResponseBodySize := some 4 })
  let atLimitRequest ← Request.new |>.method .get |>.uri! "/exact-limit"
    |>.header! "Host" "example.com" |>.empty
  let atLimitPromise ← sendInBackground atLimitAgent atLimitRequest

  let _ ← drainRequest atLimitClient
  atLimitClient.send (rawResp "200 OK"
    #[("Content-Length", "4"), ("Connection", "close")] "1234")

  match ← await atLimitPromise.result! with
  | Except.error e => throw (IO.userError s!"exact-limit response failed: {e}")
  | Except.ok resp =>
    let body ← resp.body.readAll (α := String)
    unless body == "1234" do
      throw (IO.userError s!"expected exact-limit body '1234', got {body.quote}")

  let (overLimitClient, overLimitServer) ← Mock.new
  let overLimitAgent ← mkAgent overLimitServer (config := { maxResponseBodySize := some 4 })
  let overLimitRequest ← Request.new |>.method .get |>.uri! "/one-over-limit"
    |>.header! "Host" "example.com" |>.empty
  let overLimitPromise ← sendInBackground overLimitAgent overLimitRequest

  let _ ← drainRequest overLimitClient
  overLimitClient.send (rawResp "200 OK"
    #[("Content-Length", "5"), ("Connection", "close")] "12345")

  match ← await overLimitPromise.result! with
  | Except.error _ => pure ()
  | Except.ok resp =>
    let result : Except String String ← try
        pure (Except.ok (← resp.body.readAll (α := String)))
      catch e => pure (Except.error (toString e))
    match result with
    | Except.error _ => pure ()
    | Except.ok body =>
      throw (IO.userError s!"limit+1 response unexpectedly succeeded with {body.quote}")

-- The body-size counter must reset on `.next` so a second keep-alive response
-- is checked against its own size, not the cumulative bytes from the previous
-- response.

#eval show IO _ from runWithTimeout "maxResponseBodySize resets between keep-alive requests" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let agent ← mkAgent mockServer (config := { maxResponseBodySize := some 4 })

  let req1 ← Request.new |>.method .get |>.uri! "/first"
    |>.header! "Host" "example.com" |>.empty
  let p1 ← sendInBackground agent req1

  let _ ← drainRequest mockClient
  mockClient.send (rawResp "200 OK"
    #[("Content-Length", "4"), ("Connection", "keep-alive")] "1234")

  match ← await p1.result! with
  | Except.error e => throw (IO.userError s!"first request failed: {e}")
  | Except.ok resp =>
    let body ← resp.body.readAll (α := String)
    unless body == "1234" do
      throw (IO.userError s!"expected first body '1234', got {body.quote}")

  let req2 ← Request.new |>.method .get |>.uri! "/second"
    |>.header! "Host" "example.com" |>.empty
  let p2 ← sendInBackground agent req2

  let _ ← drainRequest mockClient
  mockClient.send (rawResp "200 OK"
    #[("Content-Length", "2"), ("Connection", "close")] "ok")

  match ← await p2.result! with
  | Except.error e => throw (IO.userError s!"second request failed: {e}")
  | Except.ok resp =>
    let body ← resp.body.readAll (α := String)
    unless body == "ok" do
      throw (IO.userError s!"expected second body 'ok', got {body.quote}")

-- An unfollowed 3xx response is caller-facing, so its body must still respect
-- `maxResponseBodySize` rather than the internal redirect drain limit.

#eval show IO _ from runWithTimeout "maxResponseBodySize applies to unfollowed 302 body" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let agent ← mkAgent mockServer (config := { maxRedirects := 0, maxResponseBodySize := some 5 })

  let request ← Request.new |>.method .get |>.uri! "/"
    |>.header! "Host" "example.com" |>.empty

  let resultPromise ← sendInBackground agent request

  let _ ← drainRequest mockClient
  mockClient.send (rawResp "302 Found"
    #[("Location", "/next"),
      ("Content-Length", "10"),
      ("Connection", "close")] "0123456789")

  match ← await resultPromise.result! with
  | Except.error e => throw (IO.userError s!"agent errored before returning 302: {e}")
  | Except.ok resp =>
    unless resp.line.status.toCode == 302 do
      throw (IO.userError s!"expected 302, got {resp.line.status.toCode}")
    let got : Except String String ← try
        let s ← resp.body.readAll (α := String)
        pure (Except.ok s)
      catch e => pure (Except.error (toString e))
    match got with
    | Except.error _ => pure ()
    | Except.ok s =>
      if s.toUTF8.size > 5 then
        throw (IO.userError s!"unfollowed 302 ignored maxResponseBodySize and returned {s.toUTF8.size} bytes")

-- A status rejection that drains the body must not strand unread body bytes on the session.
-- After the error, the same keep-alive connection should still handle the next request.

#eval show IO _ from runWithTimeout "status rejection preserves keep-alive reuse" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let agent ← mkAgent mockServer

  let badReq ← Request.new |>.method .get |>.uri! "/bad"
    |>.header! "Host" "example.com" |>.empty
  let badPromise ← sendInBackground agent badReq

  let _ ← drainRequest mockClient
  mockClient.send (rawResp "404 Not Found"
    #[("Content-Length", "5"),
      ("Connection", "keep-alive")] "error")

  -- Caller checks status and drains body before reusing the connection.
  match ← await badPromise.result! with
  | Except.error e => throw (IO.userError s!"unexpected send error: {e}")
  | Except.ok resp =>
    unless resp.line.status.toCode == 404 do
      throw (IO.userError "expected 404")
    discard <| resp.body.readAll (α := ByteArray)

  let goodReq ← Request.new |>.method .get |>.uri! "/good"
    |>.header! "Host" "example.com" |>.empty
  let goodPromise ← sendInBackground agent goodReq

  let goodBytes ← drainRequest mockClient
  mockClient.send (rawResp "200 OK"
    #[("Content-Length", "2"),
      ("Connection", "close")] "ok")

  match ← await goodPromise.result! with
  | Except.error e => throw (IO.userError s!"follow-up request failed after status rejection: {e}")
  | Except.ok resp =>
    let body ← resp.body.readAll (α := String)
    unless body == "ok" do
      throw (IO.userError s!"expected follow-up body 'ok', got {body.quote}")

  let goodText := String.fromUTF8! goodBytes
  unless goodText.startsWith "GET /good" do
    throw <| IO.userError
      s!"follow-up request never reached the wire after status rejection:\n{goodText.quote}"

-- ============================================================
-- Section 8 — Methods that do not carry a body
-- ============================================================

-- A HEAD response with `Content-Length: N` must not cause the client to wait for N
-- body bytes (RFC 9110 §8.6); the response should be delivered and the connection
-- reusable.

#eval show IO _ from runWithTimeout "HEAD response with Content-Length has no body" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let agent ← mkAgent mockServer

  let req ← Request.new |>.method .head |>.uri! "/doc.html"
    |>.header! "Host" "example.com" |>.empty
  let p ← sendInBackground agent req

  let _ ← drainRequest mockClient
  mockClient.send (rawResp "200 OK"
    #[("Content-Length", "1234"), ("Connection", "keep-alive")] "")

  match ← await p.result! with
  | Except.error e => throw (IO.userError s!"HEAD request failed: {e}")
  | Except.ok resp =>
    unless resp.line.status.toCode == 200 do
      throw (IO.userError s!"expected 200, got {resp.line.status.toCode}")

  let req2 ← Request.new |>.method .get |>.uri! "/follow"
    |>.header! "Host" "example.com" |>.empty
  let p2 ← sendInBackground agent req2

  let _ ← drainRequest mockClient
  mockClient.send (rawResp "200 OK"
    #[("Content-Length", "2"), ("Connection", "close")] "ok")

  match ← await p2.result! with
  | Except.error e => throw (IO.userError s!"follow-up GET after HEAD failed: {e}")
  | Except.ok _ => pure ()

-- A 204 No Content response has no body regardless of framing headers. Keep-alive
-- must be preserved so a second request on the same connection succeeds.

#eval show IO _ from runWithTimeout "204 No Content supports keep-alive" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let agent ← mkAgent mockServer

  let req ← Request.new |>.method .delete |>.uri! "/item/1"
    |>.header! "Host" "example.com" |>.empty
  let p ← sendInBackground agent req

  let _ ← drainRequest mockClient
  mockClient.send "HTTP/1.1 204 No Content\r\nConnection: keep-alive\r\n\r\n".toUTF8

  match ← await p.result! with
  | Except.error e => throw (IO.userError s!"DELETE failed: {e}")
  | Except.ok resp =>
    unless resp.line.status.toCode == 204 do
      throw (IO.userError s!"expected 204, got {resp.line.status.toCode}")

  let req2 ← Request.new |>.method .get |>.uri! "/other"
    |>.header! "Host" "example.com" |>.empty
  let p2 ← sendInBackground agent req2

  let _ ← drainRequest mockClient
  mockClient.send (rawResp "200 OK"
    #[("Content-Length", "2"), ("Connection", "close")] "ok")

  match ← await p2.result! with
  | Except.error e => throw (IO.userError s!"follow-up after 204 failed: {e}")
  | Except.ok _ => pure ()

-- ============================================================
-- Section 11 — Server closes mid-response body
-- ============================================================
-- If the server drops the connection after headers but before the full body,
-- reading the body must surface an error rather than silently returning
-- truncated data — otherwise a caller cannot tell a complete 3-byte body from a
-- truncated 10-byte body.

#eval show IO _ from runWithTimeout "server close mid-body errors body read" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let agent ← mkAgent mockServer

  let req ← Request.new |>.method .get |>.uri! "/short"
    |>.header! "Host" "example.com" |>.empty
  let p ← sendInBackground agent req

  let _ ← drainRequest mockClient
  mockClient.send "HTTP/1.1 200 OK\r\nContent-Length: 10\r\nConnection: close\r\n\r\n".toUTF8
  mockClient.send "abc".toUTF8
  mockClient.close

  match ← await p.result! with
  | Except.error _ => pure ()
  | Except.ok resp =>
    let got : Except String String ← try
        let s ← resp.body.readAll (α := String)
        pure (Except.ok s)
      catch e => pure (Except.error (toString e))
    match got with
    | Except.ok s =>
      if s.toUTF8.size == 10 then
        pure ()
      else
        throw (IO.userError s!"partial body silently returned ({s.toUTF8.size} of 10 bytes, expected error)")
    | Except.error _ => pure ()

-- ============================================================
-- Section 12 — Default User-Agent is present
-- ============================================================
-- The default `Config.userAgent` ("lean-http/1.1") must be injected when the
-- request does not set one.

#eval show IO _ from runWithTimeout "default User-Agent injected" 3000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let agent ← mkAgent mockServer

  let req ← Request.new |>.method .get |>.uri! "/"
    |>.header! "Host" "example.com" |>.empty
  let p ← sendInBackground agent req

  let firstBytes ← drainRequest mockClient
  mockClient.send (rawResp "200 OK"
    #[("Content-Length", "0"), ("Connection", "close")] "")

  match ← await p.result! with
  | Except.error e => throw (IO.userError s!"agent error: {e}")
  | Except.ok _ => pure ()

  let reqText := String.fromUTF8! firstBytes
  unless reqText.toLower.contains "user-agent:" do
    throw <| IO.userError
      s!"default User-Agent must be present:\n{reqText.quote}"

-- ============================================================
-- Section 13 — Streaming request body uses chunked encoding
-- ============================================================
-- A request body whose size is not known in advance (`.stream`) must be framed
-- with `Transfer-Encoding: chunked`, not a bogus Content-Length.

#eval show IO _ from runWithTimeout "stream body uses Transfer-Encoding: chunked" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let agent ← mkAgent mockServer

  let req ← Request.new |>.method .post |>.uri! "/upload"
    |>.header! "Host" "example.com"
    |>.stream (fun out => do
      out.send (Chunk.ofByteArray "part-1".toUTF8)
      out.send (Chunk.ofByteArray "part-2".toUTF8)
      out.close)
  let p ← sendInBackground agent req

  let firstBytes ← drainRequest mockClient
  mockClient.send (rawResp "200 OK"
    #[("Content-Length", "2"), ("Connection", "close")] "ok")

  match ← await p.result! with
  | Except.error e => throw (IO.userError s!"agent error: {e}")
  | Except.ok _ => pure ()

  let reqText := String.fromUTF8! firstBytes
  let lower := reqText.toLower
  unless lower.contains "transfer-encoding: chunked" do
    throw <| IO.userError
      s!"stream body must use chunked encoding:\n{reqText.quote}"
  if lower.contains "content-length:" then
    throw <| IO.userError
      s!"stream body must NOT have Content-Length:\n{reqText.quote}"
  -- The chunked body must carry both parts and end with the zero chunk.
  unless lower.endsWith "0\r\n\r\n" do
    throw <| IO.userError
      s!"chunked body must terminate with 0\\r\\n\\r\\n:\n{reqText.quote}"
  unless reqText.contains "part-1" && reqText.contains "part-2" do
    throw <| IO.userError
      s!"chunked body must contain all streamed parts:\n{reqText.quote}"
