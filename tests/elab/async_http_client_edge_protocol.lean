module

import Std.Http.Test.Helpers

/-! HTTP client wire-protocol, framing, response-limit, and body-stream edge cases. -/

open Std.Async
open Std Http Internal
open Test.ClientHelpers

-- ============================================================
-- Section 4 — Expect: 100-continue
-- ============================================================

-- Happy path: server sends 100, client pumps body, server sends 200.

#eval show IO _ from runWithTimeout "Expect: 100-continue happy path sends body after 100" 4000 <|
  Async.block do
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

  -- The head and a wrongly-released body go out in separate writes, so the read above can stop
  -- between them. Settle well inside the default `expectContinueTimeout` and probe the wire again.
  IO.sleep 100
  if let some early ← mockClient.tryRecv? then
    throw <| IO.userError
      s!"client sent body before 100 Continue:\n{(String.fromUTF8! early).quote}"

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

#eval show IO _ from runWithTimeout "Expect: 100-continue 417 rejection discards body" 4000 <|
  Async.block do
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

  -- The rejection is a complete, valid response, so it belongs to the caller: an error here would
  -- mean the abandoned body took the exchange down with it.
  match ← await resultPromise.result! with
  | Except.error e => throw (IO.userError s!"a 417 rejection surfaced as an error: {e}")
  | Except.ok resp =>
    resp.body.close
    unless resp.line.status.toCode == 417 do
      throw <| IO.userError s!"expected 417, got {resp.line.status.toCode}"

  -- Give the drain task a brief moment to observe any stray writes.
  IO.sleep 50
  if ← leakedRef.get then
    throw (IO.userError "body was sent after 417 Expectation Failed")

-- Server bypass: no 100 is sent, the server jumps straight to a 2xx response
-- before the body has been pumped. The pending body must be discarded so the
-- connection is not stuck.

#eval show IO _ from
  runWithTimeout "Expect: 100-continue bypass with early 200 discards pending body" 4000 <|
  Async.block do
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

  let _ ← drainRequest mockClient
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

  let _ ← drainRequest mockClient
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

#eval show IO _ from runWithTimeout "maxResponseBodySize exceeded errors the request" 4000 <|
  Async.block do
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

  -- The limit is enforced over decoded body chunks, which are only pulled after `.endHeaders` has
  -- already resolved the caller's promise, so the head is always delivered and the failure always
  -- arrives through the body. Accepting an up-front error instead would let a regression that
  -- withholds the head pass unnoticed.
  match ← await resultPromise.result! with
  | Except.error e =>
    throw (IO.userError s!"the response head was not delivered before the limit fired: {e}")
  | Except.ok resp =>
    -- Handing back the first 4 bytes as if that were the whole body is the failure this guards
    -- against: the caller cannot tell it from a complete 4-byte response.
    let got : Except String String ← try
        let s ← resp.body.readAll (α := String)
        pure (Except.ok s)
      catch e => pure (Except.error (toString e))
    match got with
    | Except.ok s =>
      throw (IO.userError
        s!"an over-limit body was returned as {s.toUTF8.size} bytes instead of failing the read")
    | Except.error _ => pure ()

-- The response-body limit is inclusive: exactly `maxResponseBodySize` bytes are accepted, while
-- the first byte beyond the limit fails the stream.
#eval show IO _ from runWithTimeout "maxResponseBodySize exact boundary is inclusive" 4000 <|
  Async.block do
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

  -- As above, the head is delivered and only the body read may fail.
  match ← await overLimitPromise.result! with
  | Except.error e =>
    throw (IO.userError s!"the limit+1 response head was not delivered: {e}")
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

#eval show IO _ from runWithTimeout "maxResponseBodySize resets between keep-alive requests" 4000 <|
  Async.block do
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

#eval show IO _ from runWithTimeout "maxResponseBodySize applies to unfollowed 302 body" 4000 <|
  Async.block do
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
    -- The 10-byte body is over the 5-byte limit, so the read must fail rather than hand back a
    -- silently truncated prefix.
    let got : Except String String ← try
        let s ← resp.body.readAll (α := String)
        pure (Except.ok s)
      catch e => pure (Except.error (toString e))
    match got with
    | Except.error _ => pure ()
    | Except.ok s =>
      throw (IO.userError
        s!"unfollowed 302 ignored maxResponseBodySize and returned {s.toUTF8.size} bytes")

-- An error status is an ordinary response: its body is delivered to the caller like any other, and
-- once drained the same keep-alive connection must still carry the next request.

#eval show IO _ from runWithTimeout "an error status preserves keep-alive reuse" 4000 <|
  Async.block do
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
  | Except.error e => throw (IO.userError s!"follow-up request failed after a 404: {e}")
  | Except.ok resp =>
    let body ← resp.body.readAll (α := String)
    unless body == "ok" do
      throw (IO.userError s!"expected follow-up body 'ok', got {body.quote}")

  let goodText := String.fromUTF8! goodBytes
  unless goodText.startsWith "GET /good" do
    throw <| IO.userError
      s!"follow-up request never reached the wire after a 404:\n{goodText.quote}"

-- ============================================================
-- Section 8 — Methods that do not carry a body
-- ============================================================

-- A HEAD response with `Content-Length: N` must not cause the client to wait for N
-- body bytes (RFC 9110 §8.6); the response should be delivered and the connection
-- reusable.

#eval show IO _ from runWithTimeout "HEAD response with Content-Length has no body" 4000 <|
  Async.block do
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

  -- The head arrives in its own write, well before the truncation is observable, so it must reach
  -- the caller; the failure belongs to the body read.
  match ← await p.result! with
  | Except.error e =>
    throw (IO.userError s!"the response head was not delivered before the peer vanished: {e}")
  | Except.ok resp =>
    -- Only 3 of the declared 10 bytes were ever sent, so any successful read is a short read.
    let got : Except String String ← try
        let s ← resp.body.readAll (α := String)
        pure (Except.ok s)
      catch e => pure (Except.error (toString e))
    match got with
    | Except.ok s =>
      throw (IO.userError
        s!"partial body silently returned ({s.toUTF8.size} of 10 bytes, expected error)")
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

#eval show IO _ from runWithTimeout "stream body uses Transfer-Encoding: chunked" 4000 <|
  Async.block do
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
  -- Both parts must be chunk-framed with their own size line. (`drainRequest` only returns once
  -- the bytes end with the zero chunk, so asserting the terminator here would prove nothing.)
  unless reqText.contains "6\r\npart-1\r\n" && reqText.contains "6\r\npart-2\r\n" do
    throw <| IO.userError
      s!"chunked body must carry each streamed part with its own size line:\n{reqText.quote}"

-- ============================================================
-- Section 16 — Response-body limits and bodyless request framing
-- ============================================================

-- `maxResponseBodySize` is the only cap that decides a response body. The HTTP/1.1 machine used to
-- carry its own 64 MiB `maxBodySize` default, which silently overrode the configured limit and
-- rejected a larger response with a protocol-level `Entity too large` before a single body byte
-- was on the wire.

#eval show IO _ from
  runWithTimeout "maxResponseBodySize none accepts a response above the H1 default" 4000 <|
  Async.block do
  let (mockClient, mockServer) ← Mock.new
  let agent ← mkAgent mockServer

  let req ← Request.new |>.method .get |>.uri! "/big"
    |>.header! "Host" "example.com" |>.empty
  let p ← sendInBackground agent req

  let _ ← drainRequest mockClient
  -- 64 MiB + 1, declared but never sent: the header alone decides.
  mockClient.send "HTTP/1.1 200 OK\r\nContent-Length: 67108865\r\nConnection: close\r\n\r\n".toUTF8

  match ← await p.result! with
  | Except.error e =>
    throw <| IO.userError s!"client with no response-body limit rejected a 64 MiB+1 response: {e}"
  | Except.ok resp =>
    unless resp.line.status == .ok do
      throw <| IO.userError s!"expected 200, got {resp.line.status.toCode}"

-- Raising `maxResponseBodySize` past that old ceiling must work too.

#eval show IO _ from
  runWithTimeout "explicit maxResponseBodySize above the H1 default is honoured" 4000 <|
  Async.block do
  let (mockClient, mockServer) ← Mock.new
  let agent ← mkAgent mockServer (config := { maxResponseBodySize := some 1073741824 })

  let req ← Request.new |>.method .get |>.uri! "/big"
    |>.header! "Host" "example.com" |>.empty
  let p ← sendInBackground agent req

  let _ ← drainRequest mockClient
  mockClient.send "HTTP/1.1 200 OK\r\nContent-Length: 67108865\r\nConnection: close\r\n\r\n".toUTF8

  match ← await p.result! with
  | Except.error e =>
    throw <| IO.userError
      s!"client with a 1 GiB maxResponseBodySize rejected a 64 MiB+1 response: {e}"
  | Except.ok resp =>
    unless resp.line.status == .ok do
      throw <| IO.userError s!"expected 200, got {resp.line.status.toCode}"

-- RFC 9112 §3.2: "A client MUST send a Host header field in all HTTP/1.1 request messages."
-- `Agent` and `Pool` both carry the target `URI.Origin`, so a request built without one must not
-- reach the wire bare.

#eval show IO _ from
  runWithTimeout "client supplies Host from the origin when the request omits it" 4000 <|
  Async.block do
  let (mockClient, mockServer) ← Mock.new
  let agent ← mkAgent mockServer

  let req ← Request.new |>.method .get |>.uri! "/nohost" |>.empty
  let p ← sendInBackground agent req

  let reqBytes ← drainRequest mockClient
  mockClient.send (rawResp "200 OK" #[("Content-Length", "2"), ("Connection", "close")] "ok")
  let _ ← await p.result!

  let reqText := String.fromUTF8! reqBytes
  unless reqText.contains "Host: example.com" do
    throw <| IO.userError s!"HTTP/1.1 request went out without a Host header:\n{reqText.quote}"

-- RFC 9110 §8.6: "A user agent SHOULD NOT send a Content-Length header field when the request
-- message does not contain content and the method semantics do not anticipate such data." An empty
-- POST must still send `Content-Length: 0` — there the method does anticipate content.

#eval show IO _ from
  runWithTimeout "bodyless requests do not send Content-Length" 8000 <| Async.block do
  let check (method : Method) (expectContentLength : Bool) : Async Unit := do
    let (mockClient, mockServer) ← Mock.new
    let agent ← mkAgent mockServer

    let req ← Request.new |>.method method |>.uri! "/x"
      |>.header! "Host" "example.com" |>.empty
    let p ← sendInBackground agent req

    let reqBytes ← drainRequest mockClient
    mockClient.send (rawResp "200 OK" #[("Content-Length", "2"), ("Connection", "close")] "ok")
    let _ ← await p.result!

    let reqText := String.fromUTF8! reqBytes
    let hasContentLength := reqText.toLower.contains "content-length:"
    if hasContentLength && !expectContentLength then
      throw <| IO.userError s!"bodyless {method} carried Content-Length:\n{reqText.quote}"
    if !hasContentLength && expectContentLength then
      throw <| IO.userError s!"empty {method} dropped Content-Length:\n{reqText.quote}"

  check .get false
  check .head false
  check .delete false
  check .options false
  check .post true

-- ============================================================
-- Section 17 — Incremental parsing across read boundaries
-- ============================================================

-- The reader re-parses from the same position whenever a parse runs out of input, so no single
-- construct may depend on arriving in one read. `manyItems` used to report an item that ran out of
-- input as "end of list", which made the caller's terminating `crlf` fail outright: a trailer field
-- or a chunk extension split across two reads became a protocol error on a valid response.

#eval show IO _ from
  runWithTimeout "chunked body sections survive every read boundary" 30000 <| Async.block do
  -- Replays `raw` split at every byte offset, so no boundary inside it is left untested.
  let atEverySplit (what : String) (raw : ByteArray) (expected : String) : Async Unit := do
    for split in 0...raw.size do
      let (mockClient, mockServer) ← Mock.new
      let agent ← mkAgent mockServer

      let req ← Request.new |>.method .get |>.uri! "/t"
        |>.header! "Host" "example.com" |>.empty
      let p ← sendInBackground agent req
      let _ ← drainRequest mockClient

      -- The mock joins whatever is already queued, so the second half has to wait for the reader
      -- to have taken the first: without the pause the split may never reach the parser at all.
      background do
        mockClient.send (raw.extract 0 split)
        IO.sleep 10
        mockClient.send (raw.extract split raw.size)

      match ← await p.result! with
      | Except.error e =>
        throw <| IO.userError s!"{what} split at byte {split} was rejected: {e}"
      | Except.ok resp =>
        let body ← try
            pure (Except.ok (← resp.body.readAll (α := String)))
          catch e => pure (Except.error (toString e))
        match body with
        | Except.error e =>
          throw <| IO.userError s!"{what} split at byte {split} was rejected: {e}"
        | Except.ok text =>
          unless text == expected do
            throw <| IO.userError s!"{what} split at byte {split} produced body {text.quote}"

  let head := "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\nConnection: close\r\n\r\n"
  atEverySplit "trailer" (head ++ "3\r\nabc\r\n2\r\nde\r\n0\r\nX-Trail: t\r\n\r\n").toUTF8 "abcde"
  atEverySplit "chunk extension" (head ++ "3;name=value\r\nabc\r\n0\r\n\r\n").toUTF8 "abc"

-- A malformed trailer must still be rejected once the whole section has arrived.

#eval show IO _ from
  runWithTimeout "forbidden trailer field is still rejected" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let agent ← mkAgent mockServer

  let req ← Request.new |>.method .get |>.uri! "/t"
    |>.header! "Host" "example.com" |>.empty
  let p ← sendInBackground agent req
  let _ ← drainRequest mockClient
  mockClient.send
    ("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\nConnection: close\r\n\r\n"
      ++ "2\r\nok\r\n0\r\nContent-Length: 99\r\n\r\n").toUTF8

  -- The 200 head is valid and parses before the trailer section is reached, so it reaches the
  -- caller; only the body read may fail.
  match ← await p.result! with
  | Except.error e => throw (IO.userError s!"the 200 head was not delivered: {e}")
  | Except.ok resp =>
    let body ← try
        pure (some (← resp.body.readAll (α := String)))
      catch _ => pure none
    if let some text := body then
      throw <| IO.userError s!"framing field in a trailer was accepted, body {text.quote}"

-- ============================================================
-- Section 18 — Chunk sizes above the machine's own default
-- ============================================================

-- As with `maxBodySize`, the machine's `maxChunkSize` default (8 MiB) is not a client-facing
-- setting, and a chunk-size line only announces how many bytes follow. Leaving it in place
-- rejected a large-but-legal chunk with `Entity too large` on a client whose `maxResponseBodySize`
-- is `none`.

#eval show IO _ from
  runWithTimeout "a chunk above the H1 default cap is delivered" 30000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let agent ← mkAgent mockServer

  let req ← Request.new |>.method .get |>.uri! "/big"
    |>.header! "Host" "example.com" |>.empty
  let p ← sendInBackground agent req
  let _ ← drainRequest mockClient

  let size := 8 * 1024 * 1024 + 1
  let block : ByteArray := ⟨Array.replicate 65536 'x'.toUInt8⟩
  background do
    mockClient.send
      ("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\nConnection: close\r\n\r\n"
        ++ String.ofList (Nat.toDigits 16 size) ++ "\r\n").toUTF8
    let mut sent := 0
    while sent + block.size ≤ size do
      mockClient.send block
      sent := sent + block.size
    mockClient.send ⟨Array.replicate (size - sent) 'x'.toUInt8⟩
    mockClient.send "\r\n0\r\n\r\n".toUTF8

  match ← await p.result! with
  | Except.error e => throw <| IO.userError s!"client rejected an 8 MiB + 1 chunk: {e}"
  | Except.ok resp =>
    let body ← resp.body.readAll (α := ByteArray)
    unless body.size == size do
      throw <| IO.userError s!"expected {size} body bytes, got {body.size}"

-- A chunk size that does not fit in 64 bits is still rejected.

#eval show IO _ from
  runWithTimeout "a chunk size beyond 64 bits is rejected" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let agent ← mkAgent mockServer

  let req ← Request.new |>.method .get |>.uri! "/huge"
    |>.header! "Host" "example.com" |>.empty
  let p ← sendInBackground agent req
  let _ ← drainRequest mockClient
  mockClient.send
    ("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\nConnection: close\r\n\r\n"
      ++ "FFFFFFFFFFFFFFFFFFFF\r\nok\r\n0\r\n\r\n").toUTF8

  -- Same shape: the head is valid, the oversized chunk-size line is a body-read failure.
  match ← await p.result! with
  | Except.error e => throw (IO.userError s!"the 200 head was not delivered: {e}")
  | Except.ok resp =>
    let body ← try
        pure (some (← resp.body.readAll (α := String)))
      catch _ => pure none
    if let some text := body then
      throw <| IO.userError s!"a 2^80 chunk size was accepted, body {text.quote}"

-- ============================================================
-- Section 19 — A request body that fails while being sent
-- ============================================================

-- A body stream closed with an error never produced the content its framing promised. Ending the
-- chunked body with a zero chunk would hand the peer a truncated request that looks complete, so
-- the request fails instead. The connection loop learns of the failure only through the body pump;
-- a body that had already failed when the loop first looked at it must not be mistaken for one the
-- caller had finished writing.

/--
Collects everything written for a request, stopping at whichever comes first: the connection going
away (the request was abandoned) or a complete chunked body on the wire (it was not).

Both tests below wait on this rather than on the send's outcome, because a request framed as
complete leaves the client waiting for a response the peer will never send — awaiting the outcome
first would report that defect as a bare test timeout. It also makes the bytes checked the full
ones, instead of whatever a concurrent reader happened to have appended.
-/
private def settledRequestWire (mockClient : Mock.Client) : Async String := do
  let mut bytes := ByteArray.empty
  repeat
    if (String.fromUTF8! bytes).contains "0\r\n\r\n" then break
    match ← mockClient.recv? with
    | none => break
    | some chunk => bytes := bytes ++ chunk
  return String.fromUTF8! bytes

#eval show IO _ from
  runWithTimeout "a request body that failed before dispatch fails the request" 5000 <|
  Async.block do
  let (mockClient, mockServer) ← Mock.new
  let agent ← mkAgent mockServer

  let stream ← Body.mkStream
  stream.setKnownSize (some .chunked)
  stream.closeWithError (IO.userError "producer failed")

  let req := Request.Builder.body
    (Request.new |>.method .post |>.uri! "/upload" |>.header! "Host" "example.com") stream
  let p ← sendInBackground agent req

  let text ← settledRequestWire mockClient
  if text.contains "0\r\n\r\n" then
    throw <| IO.userError
      s!"a body that had already failed was terminated as a complete chunked body:\n{text.quote}"

  match ← await p.result! with
  | Except.ok resp =>
    resp.body.close
    throw <| IO.userError "a request whose body had already failed reported success"
  | Except.error _ => pure ()

-- The same holds when the producer fails partway through streaming.

#eval show IO _ from
  runWithTimeout "a request body that fails mid-stream fails the request" 5000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let agent ← mkAgent mockServer

  let req ← Request.new |>.method .post |>.uri! "/upload"
    |>.header! "Host" "example.com" |>.stream (fun s => do
      s.send { data := "partial".toUTF8, extensions := #[] } false
      IO.sleep 100
      throw (IO.userError "producer failed"))
  let p ← sendInBackground agent req

  let text ← settledRequestWire mockClient
  if text.contains "0\r\n\r\n" then
    throw <| IO.userError
      s!"a body that failed mid-stream was terminated as a complete chunked body:\n{text.quote}"

  match ← await p.result! with
  | Except.ok resp =>
    resp.body.close
    throw <| IO.userError "a request whose body failed reported success"
  | Except.error _ => pure ()

-- ============================================================
-- Section 20 — The header-block allowance follows the client's own limits
-- ============================================================

-- `maxResponseHeaders`, `maxHeaderNameSize`, and `maxHeaderValueSize` must be jointly reachable.
-- The machine's aggregate `maxHeaderBytes` default (64 KiB) is smaller than they describe, so
-- eight individually-legal 10 KiB values were rejected together.

#eval show IO _ from
  runWithTimeout "headers within the client's own limits are accepted" 5000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let agent ← mkAgent mockServer

  let req ← Request.new |>.method .get |>.uri! "/big-headers"
    |>.header! "Host" "example.com" |>.empty
  let p ← sendInBackground agent req
  let _ ← drainRequest mockClient

  let value := String.ofList (List.replicate 10000 'v')
  let hdrs := (List.range 8).toArray.map (fun i => (s!"X-H{i}", value))
  mockClient.send (rawResp "200 OK"
    (hdrs ++ #[("Content-Length", "2"), ("Connection", "close")]) "ok")

  match ← await p.result! with
  | Except.error e =>
    throw <| IO.userError s!"8 headers of 10 KiB were rejected under a 16 KiB per-value limit: {e}"
  | Except.ok resp =>
    let body ← resp.body.readAll (α := String)
    unless body == "ok" do throw <| IO.userError s!"expected 'ok', got {body.quote}"

-- A header block beyond what those limits describe is still rejected.

#eval show IO _ from
  runWithTimeout "a header block beyond the client's limits is rejected" 5000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let agent ← mkAgent mockServer (config := { maxResponseHeaders := 4, maxHeaderValueSize := 1024 })

  let req ← Request.new |>.method .get |>.uri! "/big-headers"
    |>.header! "Host" "example.com" |>.empty
  let p ← sendInBackground agent req
  let _ ← drainRequest mockClient

  let value := String.ofList (List.replicate 1000 'v')
  let hdrs := (List.range 40).toArray.map (fun i => (s!"X-H{i}", value))
  mockClient.send (rawResp "200 OK"
    (hdrs ++ #[("Content-Length", "2"), ("Connection", "close")]) "ok")

  match ← await p.result! with
  | Except.error _ => pure ()
  | Except.ok resp =>
    resp.body.close
    throw <| IO.userError "40 headers were accepted under maxResponseHeaders := 4"
