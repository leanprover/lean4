module

import Std.Http.Test.Helpers

/-! HTTP client connection-pool, keep-alive, timeout, shutdown, and retry edge cases. -/

open Std.Async
open Std Http Internal
open Test.ClientHelpers

-- ============================================================
-- Section 7 — Keep-alive and Connection: close
-- ============================================================

-- A same-origin request sent while the previous response body is unread does not wait for it: the
-- pool opens a second connection, and the unread body stays readable on the first.

#eval show IO _ from
  runWithTimeout "pool opens a second connection beside an unread response body" 4000 <|
  Async.block do
  let (mockClient1, mockServer1) ← Mock.new
  let (mockClient2, mockServer2) ← Mock.new
  let connectCount ← IO.mkRef 0

  let connect : Client.Connector := fun origin config => do
    let n ← connectCount.get
    connectCount.set (n + 1)
    match n with
    | 0 => return .ok (← Client.Connection.new mockServer1 origin config)
    | 1 => return .ok (← Client.Connection.new mockServer2 origin config)
    | _ => throw (IO.userError "pool opened more connections than expected")

  let client ← Client.new {} connect
  let some domain := URI.DomainName.ofString? "example.com"
    | throw (IO.userError "DomainName parse failed")
  let origin : URI.Origin := {
    scheme := URI.Scheme.ofString! "http"
    host := .name domain
    port := 80
  }

  let req1 ← Request.new |>.method .get |>.uri! "/one"
    |>.header! "Host" "example.com" |>.empty
  let p1 : IO.Promise (Except String (Response Body.Stream)) ← IO.Promise.new
  background do
    let result ← try
        let resp ← client.send origin req1
        pure (Except.ok resp)
      catch e => pure (Except.error (toString e))
    discard <| p1.resolve result

  let _ ← drainRequest mockClient1
  mockClient1.send (rawResp "200 OK"
    #[("Content-Length", "5"), ("Connection", "keep-alive")] "hello")

  let resp1 ← match ← await p1.result! with
    | Except.error e => throw (IO.userError s!"first pooled request failed: {e}")
    | Except.ok resp => pure resp

  let req2 ← Request.new |>.method .get |>.uri! "/two"
    |>.header! "Host" "example.com" |>.empty
  let p2 : IO.Promise (Except String (Response Body.Stream)) ← IO.Promise.new
  background do
    let result ← try
        let resp ← client.send origin req2
        pure (Except.ok resp)
      catch e => pure (Except.error (toString e))
    discard <| p2.resolve result

  let secondBytes ← drainRequest mockClient2
  if let some bytes ← mockClient1.tryRecv? then
    throw (IO.userError
      s!"a request went out behind the unread body:\n{(String.fromUTF8! bytes).quote}")
  mockClient2.send (rawResp "200 OK"
    #[("Content-Length", "3"), ("Connection", "close")] "two")

  match ← await p2.result! with
  | Except.error e => throw (IO.userError s!"second pooled request failed: {e}")
  | Except.ok resp2 =>
    let body ← resp2.body.readAll (α := String)
    unless body == "two" do
      throw (IO.userError s!"expected second body 'two', got {body.quote}")

  let secondText := String.fromUTF8! secondBytes
  unless secondText.startsWith "GET /two" do
    throw <| IO.userError s!"second request did not use the second connection:\n{secondText.quote}"

  let body1 ← resp1.body.readAll (α := String)
  unless body1 == "hello" do
    throw (IO.userError s!"the unread first body was lost: {body1.quote}")

-- Once the caller closes an unread pooled response body, the connection loop
-- drains the wire body and reports completion. The pool should then park the
-- connection as idle instead of opening a new one.

#eval show IO _ from
  runWithTimeout "pool reuses connection after unread response body is closed" 4000 <|
  Async.block do
  let (mockClient1, mockServer1) ← Mock.new
  let (_mockClient2, mockServer2) ← Mock.new
  let connectCount ← IO.mkRef 0

  let connect : Client.Connector := fun origin config => do
    let n ← connectCount.get
    connectCount.set (n + 1)
    match n with
    | 0 => return .ok (← Client.Connection.new mockServer1 origin config)
    | 1 => return .ok (← Client.Connection.new mockServer2 origin config)
    | _ => throw (IO.userError "pool opened more connections than expected")

  let client ← Client.new {} connect
  let some domain := URI.DomainName.ofString? "example.com"
    | throw (IO.userError "DomainName parse failed")
  let origin : URI.Origin := {
    scheme := URI.Scheme.ofString! "http"
    host := .name domain
    port := 80
  }

  let req1 ← Request.new |>.method .get |>.uri! "/one"
    |>.header! "Host" "example.com" |>.empty
  let p1 : IO.Promise (Except String (Response Body.Stream)) ← IO.Promise.new
  background do
    let result ← try
        let resp ← client.send origin req1
        pure (Except.ok resp)
      catch e => pure (Except.error (toString e))
    discard <| p1.resolve result

  let _ ← drainRequest mockClient1
  mockClient1.send (rawResp "200 OK"
    #[("Content-Length", "5"), ("Connection", "keep-alive")] "hello")

  let resp1 ← match ← await p1.result! with
    | Except.error e => throw (IO.userError s!"first pooled request failed: {e}")
    | Except.ok resp => pure resp

  resp1.body.close
  IO.sleep 50

  let req2 ← Request.new |>.method .get |>.uri! "/two"
    |>.header! "Host" "example.com" |>.empty
  let p2 : IO.Promise (Except String (Response Body.Stream)) ← IO.Promise.new
  background do
    let result ← try
        let resp ← client.send origin req2
        pure (Except.ok resp)
      catch e => pure (Except.error (toString e))
    discard <| p2.resolve result

  IO.sleep 50
  if (← connectCount.get) != 1 then
    mockClient1.close
    throw (IO.userError "pool opened a second connection after the first response body was closed")

  let secondBytes ← drainRequest mockClient1
  mockClient1.send (rawResp "200 OK"
    #[("Content-Length", "3"), ("Connection", "close")] "two")

  match ← await p2.result! with
  | Except.error e => throw (IO.userError s!"second pooled request failed: {e}")
  | Except.ok resp2 =>
    let body ← resp2.body.readAll (α := String)
    unless body == "two" do
      throw (IO.userError s!"expected second body 'two', got {body.quote}")

  let secondText := String.fromUTF8! secondBytes
  unless secondText.startsWith "GET /two" do
    throw <| IO.userError s!"second request did not reuse the first connection:\n{secondText.quote}"

-- A zero-length pooled response still needs to drive the connection through
-- completion so the connection is returned to idle.

#eval show IO _ from
  runWithTimeout "pool reuses connection after zero-length response body completes" 4000 <|
  Async.block do
  let (mockClient1, mockServer1) ← Mock.new
  let (_mockClient2, mockServer2) ← Mock.new
  let connectCount ← IO.mkRef 0

  let connect : Client.Connector := fun origin config => do
    let n ← connectCount.get
    connectCount.set (n + 1)
    match n with
    | 0 => return .ok (← Client.Connection.new mockServer1 origin config)
    | 1 => return .ok (← Client.Connection.new mockServer2 origin config)
    | _ => throw (IO.userError "pool opened more connections than expected")

  let client ← Client.new {} connect
  let some domain := URI.DomainName.ofString? "example.com"
    | throw (IO.userError "DomainName parse failed")
  let origin : URI.Origin := {
    scheme := URI.Scheme.ofString! "http"
    host := .name domain
    port := 80
  }

  let req1 ← Request.new |>.method .get |>.uri! "/empty"
    |>.header! "Host" "example.com" |>.empty
  let p1 : IO.Promise (Except String (Response Body.Stream)) ← IO.Promise.new
  background do
    let result ← try
        let resp ← client.send origin req1
        pure (Except.ok resp)
      catch e => pure (Except.error (toString e))
    discard <| p1.resolve result

  let _ ← drainRequest mockClient1
  mockClient1.send (rawResp "200 OK"
    #[("Content-Length", "0"), ("Connection", "keep-alive")] "")

  match ← await p1.result! with
  | Except.error e => throw (IO.userError s!"first pooled request failed: {e}")
  | Except.ok resp1 =>
    let body ← resp1.body.readAll (α := String)
    unless body == "" do
      throw (IO.userError s!"expected empty first body, got {body.quote}")

  IO.sleep 50

  let req2 ← Request.new |>.method .get |>.uri! "/two"
    |>.header! "Host" "example.com" |>.empty
  let p2 : IO.Promise (Except String (Response Body.Stream)) ← IO.Promise.new
  background do
    let result ← try
        let resp ← client.send origin req2
        pure (Except.ok resp)
      catch e => pure (Except.error (toString e))
    discard <| p2.resolve result

  IO.sleep 50
  if (← connectCount.get) != 1 then
    mockClient1.close
    throw (IO.userError "pool opened a second connection after a zero-length response completed")

  let secondBytes ← drainRequest mockClient1
  mockClient1.send (rawResp "200 OK"
    #[("Content-Length", "3"), ("Connection", "close")] "two")

  match ← await p2.result! with
  | Except.error e => throw (IO.userError s!"second pooled request failed: {e}")
  | Except.ok resp2 =>
    let body ← resp2.body.readAll (α := String)
    unless body == "two" do
      throw (IO.userError s!"expected second body 'two', got {body.quote}")

  let secondText := String.fromUTF8! secondBytes
  unless secondText.startsWith "GET /two" do
    throw <| IO.userError s!"second request did not reuse the first connection:\n{secondText.quote}"

-- Each origin keeps its own connection: a request to another origin neither closes nor replaces
-- the first origin's, and the first origin's next request reuses it.

#eval show IO _ from
  runWithTimeout "pool keeps a connection per origin" 4000 <|
  Async.block do
  let (mockClient1, mockServer1) ← Mock.new
  let (mockClient2, mockServer2) ← Mock.new
  let connectCount ← IO.mkRef 0

  let connect : Client.Connector := fun origin config => do
    let n ← connectCount.get
    connectCount.set (n + 1)
    match n with
    | 0 => return .ok (← Client.Connection.new mockServer1 origin config)
    | 1 => return .ok (← Client.Connection.new mockServer2 origin config)
    | _ => throw (IO.userError "pool opened more connections than expected")

  let client ← Client.new {} connect
  let origin1 := origin "example.com"
  let origin2 := origin "other.example"

  let req1 ← Request.new |>.method .get |>.uri! "/one" |>.empty
  let p1 : IO.Promise (Except String (Response Body.Stream)) ← IO.Promise.new
  background do
    let result ← try
        let resp ← client.send origin1 req1
        pure (Except.ok resp)
      catch e => pure (Except.error (toString e))
    discard <| p1.resolve result

  let _ ← drainRequest mockClient1
  mockClient1.send (rawResp "200 OK" #[("Content-Length", "1")] "1")
  match ← await p1.result! with
  | Except.error e => throw (IO.userError s!"first-origin request failed: {e}")
  | Except.ok resp1 =>
    unless (← resp1.body.readAll (α := String)) == "1" do
      throw (IO.userError "wrong body for the first-origin request")

  let req2 ← Request.new |>.method .get |>.uri! "/two" |>.empty
  let p2 : IO.Promise (Except String (Response Body.Stream)) ← IO.Promise.new
  background do
    let result ← try
        let resp ← client.send origin2 req2
        pure (Except.ok resp)
      catch e => pure (Except.error (toString e))
    discard <| p2.resolve result

  let secondBytes ← drainRequest mockClient2
  mockClient2.send (rawResp "200 OK" #[("Content-Length", "1")] "2")
  match ← await p2.result! with
  | Except.error e => throw (IO.userError s!"second-origin request failed: {e}")
  | Except.ok resp2 =>
    unless (← resp2.body.readAll (α := String)) == "2" do
      throw (IO.userError "wrong body for the second-origin request")
  unless (String.fromUTF8! secondBytes).startsWith "GET /two" do
    throw (IO.userError "the second origin did not get its own connection")

  let req3 ← Request.new |>.method .get |>.uri! "/three" |>.empty
  let p3 : IO.Promise (Except String (Response Body.Stream)) ← IO.Promise.new
  background do
    let result ← try
        let resp ← client.send origin1 req3
        pure (Except.ok resp)
      catch e => pure (Except.error (toString e))
    discard <| p3.resolve result

  let thirdBytes ← drainRequest mockClient1
  mockClient1.send (rawResp "200 OK" #[("Content-Length", "1")] "3")
  match ← await p3.result! with
  | Except.error e => throw (IO.userError s!"the first origin's second request failed: {e}")
  | Except.ok resp3 =>
    unless (← resp3.body.readAll (α := String)) == "3" do
      throw (IO.userError "wrong body for the first origin's second request")
  unless (String.fromUTF8! thirdBytes).startsWith "GET /three" do
    throw (IO.userError "the first origin's connection was not reused")
  unless (← connectCount.get) == 2 do
    throw (IO.userError s!"expected 2 connections, got {← connectCount.get}")

-- A cross-origin redirect gives the source connection back to the pool once the redirect body is
-- read, so it survives a failure to reach the redirect target and serves the next request to its
-- origin.

#eval show IO _ from
  runWithTimeout "failed cross-origin redirect leaves the source connection reusable" 4000 <|
  Async.block do
  let (mockClient1, mockServer1) ← Mock.new
  let originalConnectCount ← IO.mkRef 0

  let connect : Client.Connector := fun origin config => do
    if toString origin.host == "other.example" then
      throw (IO.userError s!"redirect target dial failed for {origin.host}")
    else
      let n ← originalConnectCount.get
      originalConnectCount.set (n + 1)
      match n with
      | 0 => return .ok (← Client.Connection.new mockServer1 origin config)
      | _ => throw (IO.userError "opened too many original-origin connections")

  -- Retries are disabled: this test asserts the state the pool is left in after a
  -- single failed cross-origin acquire, not the retry policy.
  let client ← Client.new {} connect (maxRetries := 0)
  let some domain := URI.DomainName.ofString? "example.com"
    | throw (IO.userError "DomainName parse failed")
  let origin : URI.Origin := {
    scheme := URI.Scheme.ofString! "http"
    host := .name domain
    port := 80
  }

  let req1 ← Request.new |>.method .get |>.uri! "/start"
    |>.header! "Host" "example.com" |>.empty
  let p1 : IO.Promise (Except String (Response Body.Stream)) ← IO.Promise.new
  background do
    let result ← try
        let resp ← client.send origin req1
        pure (Except.ok resp)
      catch e => pure (Except.error (toString e))
    discard <| p1.resolve result

  let _ ← drainRequest mockClient1
  mockClient1.send (rawResp "302 Found"
    #[("Location", "http://other.example/landing"),
      ("Content-Length", "0"),
      ("Connection", "keep-alive")] "")

  match ← await p1.result! with
  | Except.ok _ =>
    mockClient1.close
    throw (IO.userError "redirect unexpectedly succeeded")
  | Except.error e =>
    unless e.contains "redirect target dial failed" do
      mockClient1.close
      throw (IO.userError s!"unexpected redirect failure: {e}")

  let req2 ← Request.new |>.method .get |>.uri! "/again"
    |>.header! "Host" "example.com" |>.empty
  let p2 : IO.Promise (Except String (Response Body.Stream)) ← IO.Promise.new
  background do
    let result ← try
        let resp ← client.send origin req2
        pure (Except.ok resp)
      catch e => pure (Except.error (toString e))
    discard <| p2.resolve result

  let secondBytes ← drainRequest mockClient1
  mockClient1.send (rawResp "200 OK"
    #[("Content-Length", "2"), ("Connection", "close")] "ok")

  match ← await p2.result! with
  | Except.error e =>
    throw (IO.userError s!"the source connection did not serve the follow-up request: {e}")
  | Except.ok resp =>
    let body ← resp.body.readAll (α := String)
    unless body == "ok" do
      throw (IO.userError s!"expected second response body 'ok', got {body.quote}")

  let secondText := String.fromUTF8! secondBytes
  unless secondText.startsWith "GET /again" do
    throw <| IO.userError
      s!"second request did not reuse the source connection:\n{secondText.quote}"
  unless (← originalConnectCount.get) == 1 do
    throw (IO.userError "the pool opened a replacement for a reusable connection")

-- Two sequential requests on the same connection must both succeed, exercising the
-- `.next` reset path in the connection state machine.

#eval show IO _ from runWithTimeout "two sequential GETs on keep-alive succeed" 4000 <|
  Async.block do
  let (mockClient, mockServer) ← Mock.new
  let client ← mkClient mockServer

  -- First request.
  let req1 ← Request.new |>.method .get |>.uri! "/one"
    |>.header! "Host" "example.com" |>.empty
  let p1 ← sendInBackground client req1

  let _ ← drainRequest mockClient
  mockClient.send (rawResp "200 OK"
    #[("Content-Length", "3"), ("Connection", "keep-alive")] "one")

  match ← await p1.result! with
  | Except.error e => throw (IO.userError s!"first request failed: {e}")
  | Except.ok resp =>
    let body ← resp.body.readAll (α := String)
    unless body == "one" do
      throw (IO.userError s!"expected 'one', got {body.quote}")

  -- Second request on same connection must succeed.
  let req2 ← Request.new |>.method .get |>.uri! "/two"
    |>.header! "Host" "example.com" |>.empty
  let p2 ← sendInBackground client req2

  let _ ← drainRequest mockClient
  mockClient.send (rawResp "200 OK"
    #[("Content-Length", "3"), ("Connection", "close")] "two")

  match ← await p2.result! with
  | Except.error e => throw (IO.userError s!"second request failed: {e}")
  | Except.ok resp =>
    let body ← resp.body.readAll (α := String)
    unless body == "two" do
      throw (IO.userError s!"expected 'two', got {body.quote}")

-- `Connection: close` on the response must close the connection; a follow-up request
-- on the same connection must error out rather than hang.

#eval show IO _ from runWithTimeout "Connection: close prevents reuse" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let client ← mkClient mockServer

  let req1 ← Request.new |>.method .get |>.uri! "/"
    |>.header! "Host" "example.com" |>.empty
  let p1 ← sendInBackground client req1

  let _ ← drainRequest mockClient
  mockClient.send (rawResp "200 OK"
    #[("Content-Length", "2"), ("Connection", "close")] "ok")

  match ← await p1.result! with
  | Except.error e => throw (IO.userError s!"first request failed: {e}")
  | Except.ok resp =>
    let _ ← resp.body.readAll (α := String)

  -- The response itself must retire the connection. Closing the mock here instead would fail the
  -- second request through a dead transport whether or not `Connection: close` was honoured.
  let mut retired := false
  for _ in [0:50] do
    if ← (← client.connection).isClosed then
      retired := true
      break
    IO.sleep 20
  unless retired do
    mockClient.close
    throw (IO.userError "the connection was still open after a Connection: close response")

  -- Second send must not hang; it must fail because the connection is closed.
  let req2 ← Request.new |>.method .get |>.uri! "/"
    |>.header! "Host" "example.com" |>.empty
  let p2 ← sendInBackground client req2

  -- Nothing reaches the wire either: a retired connection *is* one whose request channel is closed
  -- (`Connection.isClosed` reads that channel), so the send above failed before writing anything.
  match ← await p2.result! with
  | Except.ok _ =>
    throw (IO.userError "second request unexpectedly succeeded after Connection: close")
  | Except.error _ => pure ()

  mockClient.close

-- ============================================================
-- Section 12 — Request deadline and connection close
-- ============================================================

-- The absolute `requestTimeout` deadline must abort a response whose body stalls after the headers
-- arrive, surfacing the error to a caller blocked reading the body (rather than hanging until the
-- much larger per-read idle timeout).
#eval show IO _ from runWithTimeout "request deadline aborts a stalled response body" 4000 <|
  Async.block do
  let (mockClient, mockServer) ← Mock.new
  let client ← mkClient mockServer (config := { requestTimeout := ⟨300, by decide⟩ })

  let request ← Request.new
    |>.method .get
    |>.uri! "/slow"
    |>.header! "Host" "example.com"
    |>.empty

  let resultPromise ← sendInBackground client request

  let _ ← drainRequest mockClient
  -- Promise a 10-byte body but never send it: the exchange must hit the request deadline.
  mockClient.send (rawResp "200 OK"
    #[("Content-Length", "10"), ("Connection", "close")] "")

  -- The head arrives immediately and the deadline is 300ms away, so it must reach the caller;
  -- accepting an up-front error here would hide a regression that withholds the head.
  match ← await resultPromise.result! with
  | Except.error e =>
    throw (IO.userError s!"the response head was not delivered before the deadline: {e}")
  | Except.ok resp =>
    let got : Except String String ← try
        let s ← resp.body.readAll (α := String)
        pure (Except.ok s)
      catch e => pure (Except.error (toString e))
    match got with
    | Except.error _ => pure ()
    | Except.ok s =>
      throw (IO.userError s!"expected request-timeout error on stalled body, read {s.quote}")

-- Incoming progress must not re-arm the whole-request timeout. A server can keep the idle timer
-- alive by dripping bytes, but the absolute request deadline must still end the exchange.
#eval show IO _ from runWithTimeout "request deadline aborts a slow-drip response body" 4000 <|
  Async.block do
  let (mockClient, mockServer) ← Mock.new
  let client ← mkClient mockServer (config := { requestTimeout := ⟨250, by decide⟩ })

  let request ← Request.new |>.method .get |>.uri! "/slow-drip"
    |>.header! "Host" "example.com" |>.empty
  let resultPromise ← sendInBackground client request

  let _ ← drainRequest mockClient
  mockClient.send (rawResp "200 OK"
    #[("Content-Length", "5"), ("Connection", "keep-alive")] "")
  background do
    for byte in #["a", "b", "c", "d", "e"] do
      IO.sleep 100
      try mockClient.send byte.toUTF8 catch _ => pure ()

  match ← await resultPromise.result! with
  | Except.error _ => pure ()
  | Except.ok resp =>
    let result : Except String String ← try
        pure (Except.ok (← resp.body.readAll (α := String)))
      catch e => pure (Except.error (toString e))
    match result with
    | Except.error _ => pure ()
    | Except.ok body =>
      throw (IO.userError s!"slow-drip response escaped request deadline with {body.quote}")

-- `Connection.close` must abort an in-flight exchange promptly (via the connection's cancellation
-- context), not leave the caller blocked until the request timeout. The request timeout below is
-- set far beyond the test budget so that only `close` can end the request; without the context
-- wiring the background loop stays parked on the socket and this test times out.
#eval show IO _ from runWithTimeout "connection close aborts an in-flight request" 4000 <|
  Async.block do
  let (mockClient, mockServer) ← Mock.new
  let client ← mkClient mockServer (config := { requestTimeout := ⟨60000, by decide⟩ })

  let request ← Request.new
    |>.method .get
    |>.uri! "/never-answered"
    |>.header! "Host" "example.com"
    |>.empty

  let resultPromise ← sendInBackground client request

  -- Server receives the request but never responds; only close should end it.
  let _ ← drainRequest mockClient
  (← client.connection).close

  match ← await resultPromise.result! with
  | Except.error _ => pure ()
  | Except.ok _ =>
    throw (IO.userError "expected in-flight request to abort when the connection is closed")

-- Opening a transport must not hold the pool lock. The first connector is deliberately blocked; a
-- request to a second origin must enter its connector before the first is released.
#eval show IO _ from runWithTimeout "pool does not hold its lock while connecting" 4000 <|
  Async.block do
  let (_mockClient1, mockServer1) ← Mock.new
  let (_mockClient2, mockServer2) ← Mock.new
  let calls ← Std.Mutex.new 0
  let firstStarted : IO.Promise Unit ← IO.Promise.new
  let releaseFirst : IO.Promise Unit ← IO.Promise.new
  let secondEntered : IO.Promise Unit ← IO.Promise.new
  let released ← IO.mkRef false
  let secondSawReleased ← IO.mkRef true

  let connect : Client.Connector := fun origin config => do
    let callNo ← calls.atomically <| modifyGet fun n => (n, n + 1)
    if callNo == 0 then
      discard <| firstStarted.resolve ()
      await releaseFirst.result!
      return .ok (← Client.Connection.new mockServer1 origin config)
    else
      secondSawReleased.set (← released.get)
      discard <| secondEntered.resolve ()
      return .ok (← Client.Connection.new mockServer2 origin config)

  let client ← Client.new {} connect (maxRetries := 0)
  let reqA ← Request.new |>.method .get |>.uri! "/a" |>.empty
  let reqB ← Request.new |>.method .get |>.uri! "/b" |>.empty

  background do discard <| client.trySend (origin "a.example") reqA
  await firstStarted.result!
  background do discard <| client.trySend (origin "b.example") reqB
  background do
    IO.sleep 300
    released.set true
    discard <| releaseFirst.resolve ()

  await secondEntered.result!
  if ← secondSawReleased.get then
    throw (IO.userError "the second connection was blocked behind the pool lock")

-- Idempotent requests retry a connector failure, including a failure before a `Connection` exists.
#eval show IO _ from runWithTimeout "GET retries after the first connection attempt fails" 4000 <|
  Async.block do
  let (mockClient, mockServer) ← Mock.new
  let calls ← IO.mkRef 0
  let connect : Client.Connector := fun origin config => do
    let callNo ← calls.get
    calls.set (callNo + 1)
    if callNo == 0 then
      throw (IO.userError "synthetic first connect failure")
    return .ok (← Client.Connection.new mockServer origin config)
  let client ← Client.new {} connect (maxRetries := 1)
  let some domain := URI.DomainName.ofString? "example.com"
    | throw (IO.userError "DomainName parse failed")
  let origin : URI.Origin := {
    scheme := URI.Scheme.ofString! "http", host := .name domain, port := 80 }
  let request ← Request.new |>.method .get |>.uri! "/retry"
    |>.header! "Host" "example.com" |>.empty
  let result : IO.Promise (Except String (Response Body.Stream)) ← IO.Promise.new

  background do
    let attempt ← try
        pure (Except.ok (← client.send origin request))
      catch e => pure (Except.error (toString e))
    discard <| result.resolve attempt
  background do
    let _ ← drainRequest mockClient
    mockClient.send (rawResp "200 OK"
      #[("Content-Length", "2"), ("Connection", "close")] "ok")

  match ← await result.result! with
  | Except.error e => throw (IO.userError s!"GET was not retried after connect failure: {e}")
  | Except.ok resp =>
    let body ← resp.body.readAll (α := String)
    unless body == "ok" do
      throw (IO.userError s!"expected retry body 'ok', got {body.quote}")
  unless (← calls.get) == 2 do
    throw (IO.userError s!"expected two connection attempts, got {← calls.get}")

-- A non-idempotent request is never retried after the peer drops the first connection mid-flight.
#eval show IO _ from runWithTimeout "POST is not retried after a mid-flight connection drop" 4000 <|
  Async.block do
  let (mockClient1, mockServer1) ← Mock.new
  let (_mockClient2, mockServer2) ← Mock.new
  let calls ← IO.mkRef 0
  let connect : Client.Connector := fun origin config => do
    let callNo ← calls.get
    calls.set (callNo + 1)
    let mockServer := if callNo == 0 then mockServer1 else mockServer2
    return .ok (← Client.Connection.new mockServer origin config)
  let client ← Client.new {} connect (maxRetries := 3)
  let some domain := URI.DomainName.ofString? "example.com"
    | throw (IO.userError "DomainName parse failed")
  let origin : URI.Origin := {
    scheme := URI.Scheme.ofString! "http", host := .name domain, port := 80 }
  let request ← Request.new |>.method .post |>.uri! "/side-effect"
    |>.header! "Host" "example.com" |>.text "payload"
  let result : IO.Promise (Except String (Response Body.Stream)) ← IO.Promise.new

  background do
    let attempt ← try
        pure (Except.ok (← client.send origin request))
      catch e => pure (Except.error (toString e))
    discard <| result.resolve attempt
  let _ ← drainRequest mockClient1
  mockClient1.close

  match ← await result.result! with
  | Except.ok _ => throw (IO.userError "POST unexpectedly succeeded after connection drop")
  | Except.error _ => pure ()
  unless (← calls.get) == 1 do
    throw (IO.userError s!"POST was retried; expected one connection attempt, got {← calls.get}")

-- ============================================================
-- Section 14 — Retry body integrity and dead-connection detection
-- ============================================================

-- An idempotent request whose streaming body was consumed by the failed attempt must NOT be
-- retried: the body cannot be replayed, so a retry would silently send an empty body.
#eval show IO _ from runWithTimeout "PUT with non-replayable stream body is not retried" 4000 <|
  Async.block do
  let (mockClient1, mockServer1) ← Mock.new
  let (mockClient2, mockServer2) ← Mock.new
  let calls ← IO.mkRef 0
  let connect : Client.Connector := fun origin config => do
    let callNo ← calls.get
    calls.set (callNo + 1)
    let mockServer := if callNo == 0 then mockServer1 else mockServer2
    return .ok (← Client.Connection.new mockServer origin config)
  let client ← Client.new {} connect (maxRetries := 3)
  let some domain := URI.DomainName.ofString? "example.com"
    | throw (IO.userError "DomainName parse failed")
  let origin : URI.Origin := {
    scheme := URI.Scheme.ofString! "http", host := .name domain, port := 80 }
  let request ← Request.new |>.method .put |>.uri! "/upload"
    |>.header! "Host" "example.com"
    |>.stream (fun out => do
        out.send (Chunk.ofByteArray "payload".toUTF8)
        out.close)
  let result : IO.Promise (Except String (Response Body.Stream)) ← IO.Promise.new

  background do
    let attempt ← try
        pure (Except.ok (← client.send origin request))
      catch e => pure (Except.error (toString e))
    discard <| result.resolve attempt

  -- Drain the first request fully (chunked or Content-Length framing), then drop the connection
  -- without responding, after the body has been consumed from the caller's stream.
  let mut firstBytes := ByteArray.empty
  repeat
    let some chunk ← mockClient1.recv?
      | throw (IO.userError "connection closed before first PUT arrived")
    firstBytes := firstBytes ++ chunk
    let t := String.fromUTF8! firstBytes
    if t.endsWith "0\r\n\r\n" || t.endsWith "payload" then break
  mockClient1.close

  -- If the client (incorrectly) retries, answer the second connection so the test fails fast on
  -- the `calls` assertion instead of timing out.
  background do
    if (← mockClient2.recv?).isSome then
      mockClient2.send (rawResp "200 OK"
        #[("Content-Length", "2"), ("Connection", "close")] "ok")

  match ← await result.result! with
  | Except.ok _ =>
    throw (IO.userError "PUT with a consumed stream body unexpectedly succeeded via retry")
  | Except.error _ => pure ()
  let attempts ← calls.get
  unless attempts == 1 do
    throw (IO.userError
      s!"PUT with non-replayable body was retried; expected 1 attempt, got {attempts}")

-- A replayable (`Body.Full`) request body must be reset before a retry so the second attempt
-- sends the complete payload again, not the consumed remainder.
#eval show IO _ from runWithTimeout "retried PUT resends the full replayable body" 4000 <|
  Async.block do
  let (mockClient1, mockServer1) ← Mock.new
  let (mockClient2, mockServer2) ← Mock.new
  let calls ← IO.mkRef 0
  let connect : Client.Connector := fun origin config => do
    let callNo ← calls.get
    calls.set (callNo + 1)
    let mockServer := if callNo == 0 then mockServer1 else mockServer2
    return .ok (← Client.Connection.new mockServer origin config)
  let client ← Client.new {} connect (maxRetries := 1)
  let some domain := URI.DomainName.ofString? "example.com"
    | throw (IO.userError "DomainName parse failed")
  let origin : URI.Origin := {
    scheme := URI.Scheme.ofString! "http", host := .name domain, port := 80 }
  let request ← Request.new |>.method .put |>.uri! "/upload"
    |>.header! "Host" "example.com" |>.text "payload"
  let result : IO.Promise (Except String (Response Body.Stream)) ← IO.Promise.new

  background do
    let attempt ← try
        pure (Except.ok (← client.send origin request))
      catch e => pure (Except.error (toString e))
    discard <| result.resolve attempt

  -- First attempt: consume the whole request (headers + body), then drop without responding.
  let _ ← drainRequest mockClient1
  mockClient1.close

  -- Second attempt: the retried request must carry the full body again.
  let retryBytes ← drainRequest mockClient2
  mockClient2.send (rawResp "200 OK"
    #[("Content-Length", "2"), ("Connection", "close")] "ok")

  match ← await result.result! with
  | Except.error e => throw (IO.userError s!"retried PUT failed: {e}")
  | Except.ok resp =>
    let _ ← resp.body.readAll (α := String)
  unless (← calls.get) == 2 do
    throw (IO.userError s!"expected two connection attempts, got {← calls.get}")
  let retryText := String.fromUTF8! retryBytes
  unless retryText.contains "payload" do
    throw <| IO.userError
      s!"retried PUT did not resend the request body:\n{retryText.quote}"

-- A pooled connection whose background loop has already shut down (idle timeout, server EOF) must
-- not be
-- handed to the next request: the request was never written to the wire, so the pool can safely
-- open a fresh connection — even for non-idempotent methods and with retries disabled.
#eval show IO _ from
  runWithTimeout "pool discards a dead connection instead of failing the next request" 4000 <|
  Async.block do
  let (mockClient1, mockServer1) ← Mock.new
  let (mockClient2, mockServer2) ← Mock.new
  let calls ← IO.mkRef 0
  let connect : Client.Connector := fun origin config => do
    let callNo ← calls.get
    calls.set (callNo + 1)
    let mockServer := if callNo == 0 then mockServer1 else mockServer2
    return .ok (← Client.Connection.new mockServer origin config)
  let client ← Client.new {} connect (maxRetries := 0)
  let some domain := URI.DomainName.ofString? "example.com"
    | throw (IO.userError "DomainName parse failed")
  let origin : URI.Origin := {
    scheme := URI.Scheme.ofString! "http", host := .name domain, port := 80 }

  -- First exchange completes cleanly; the connection is parked in the pool.
  let req1 ← Request.new |>.method .get |>.uri! "/one"
    |>.header! "Host" "example.com" |>.empty
  let p1 : IO.Promise (Except String (Response Body.Stream)) ← IO.Promise.new
  background do
    let attempt ← try
        pure (Except.ok (← client.send origin req1))
      catch e => pure (Except.error (toString e))
    discard <| p1.resolve attempt
  let _ ← drainRequest mockClient1
  mockClient1.send (rawResp "200 OK"
    #[("Content-Length", "5"), ("Connection", "keep-alive")] "hello")
  match ← await p1.result! with
  | Except.error e => throw (IO.userError s!"first pooled request failed: {e}")
  | Except.ok resp =>
    let _ ← resp.body.readAll (α := String)

  -- The server silently drops the parked connection; give the background loop
  -- time to observe EOF and shut down.
  mockClient1.close
  IO.sleep 200

  -- The next request (a POST: retries disabled and non-idempotent anyway) must transparently get
  -- a fresh connection rather than an error from the dead parked connection.
  let req2 ← Request.new |>.method .post |>.uri! "/two"
    |>.header! "Host" "example.com" |>.text "data"
  let p2 : IO.Promise (Except String (Response Body.Stream)) ← IO.Promise.new
  background do
    let attempt ← try
        pure (Except.ok (← client.send origin req2))
      catch e => pure (Except.error (toString e))
    discard <| p2.resolve attempt

  let secondBytes ← drainRequest mockClient2
  mockClient2.send (rawResp "200 OK"
    #[("Content-Length", "2"), ("Connection", "close")] "ok")

  match ← await p2.result! with
  | Except.error e => throw (IO.userError s!"POST after dead parked connection failed: {e}")
  | Except.ok resp =>
    let _ ← resp.body.readAll (α := String)
  unless (← calls.get) == 2 do
    throw (IO.userError s!"expected a fresh second connection, got {← calls.get} attempts")
  let secondText := String.fromUTF8! secondBytes
  unless secondText.startsWith "POST /two" do
    throw <| IO.userError s!"unexpected second request:\n{secondText.quote}"
