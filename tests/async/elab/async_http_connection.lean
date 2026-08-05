module

import Std.Http.Test.Helpers

open Std.Async
open Std Http Internal
open Test.ClientHelpers

/-!
Tests for `Std.Http.Client.Connection`: the client-side persistent connection and its background
exchange loop. Covers the request/response happy path, keep-alive reuse, per-request
`RequestOverrides` (including that they do not leak into the next request on the same connection),
timeouts, response body limits, `Expect: 100-continue` and informational responses, errors raised
mid-exchange, the close/shutdown surface, request queueing, and failures raised by user-supplied
request bodies.
-/

namespace ConnectionTests

open Std.Http.Client

/-- A connection whose transport is the mock client end; the test drives the peer via `Mock.Server`. -/
private def mkConnection (mockClient : Mock.Client) (config : Client.Config := {}) : Async Connection :=
  Connection.new mockClient config

private def mkRequest (method : Method) (path : String) (body : String := "")
    (extra : Array (String × String) := #[]) : Async (Request Body.Any) := do
  let mut builder := Request.new |>.method method |>.uri! path |>.header! "Host" "example.com"
  for (k, v) in extra do
    builder := builder.header! k v
  let request ← builder.text body
  pure { request with }

/-- A request whose body is a `Body.Stream` with no known size, so it is framed as chunked. -/
private def mkStreamRequest (path : String) (stream : Body.Stream)
    (extra : Array (String × String) := #[]) : Request Body.Any := Id.run do
  let mut builder := Request.new |>.method .post |>.uri! path |>.header! "Host" "example.com"
  for (k, v) in extra do
    builder := builder.header! k v
  pure { builder.body stream with }

private def emptyAny : Body.Any := Body.Any.ofBody ({} : Body.Empty)

/-- Send in the background so the test can act as the server while the exchange is in flight. -/
private def sendInBackground (connection : Connection) (request : Request Body.Any)
    (overrides : RequestOverrides := {}) :
    Async (IO.Promise (Except Error (Response Body.Stream × IO.Promise (Except Error Unit)))) := do
  let promise ← IO.Promise.new
  background do
    let result ← try connection.sendTracked request overrides
      catch e => pure (.error (.io e))
    discard <| promise.resolve result
  pure promise

/-- Read from the peer until the request head is complete, returning everything read. -/
private def readHead (mockServer : Mock.Server) : Async String := do
  let mut bytes := ByteArray.empty
  repeat
    if (String.fromUTF8! bytes).contains "\r\n\r\n" then break
    let some chunk ← mockServer.recv?
      | throw (IO.userError s!"connection closed before request head; got {(String.fromUTF8! bytes).quote}")
    bytes := bytes ++ chunk
  pure (String.fromUTF8! bytes)

/-- Read from the peer until everything seen so far contains `needle`. -/
private def readUntil (mockServer : Mock.Server) (needle : String) (seen : String := "") : Async String := do
  let mut acc := seen
  repeat
    if acc.contains needle then break
    let some chunk ← mockServer.recv?
      | throw (IO.userError s!"connection closed before {needle.quote} arrived; got {acc.quote}")
    acc := acc ++ String.fromUTF8! chunk
  pure acc

private def expectResponse (promise : IO.Promise (Except Error (Response Body.Stream × IO.Promise (Except Error Unit))))
    : Async (Response Body.Stream × IO.Promise (Except Error Unit)) := do
  match ← await promise.result! with
  | .ok pair => pure pair
  | .error e => throw (IO.userError s!"expected a response, got error: {e}")

private def expectError (promise : IO.Promise (Except Error (Response Body.Stream × IO.Promise (Except Error Unit))))
    : Async Error := do
  match ← await promise.result! with
  | .error e => pure e
  | .ok (resp, _) => throw (IO.userError s!"expected an error, got {resp.line.status.toCode}")

/-- Names the `Error` constructor, so a misclassification is visible in the failure message. -/
private def ctorName : Error → String
  | .connect m => s!".connect {m.quote}"
  | .timeout => ".timeout"
  | .closed m => s!".closed {m.quote}"
  | .protocol e => s!".protocol {e}"
  | .bodyLimitExceeded => ".bodyLimitExceeded"
  | .invalidRequest m => s!".invalidRequest {m.quote}"
  | .io e => s!".io {e}"

/--
A pool's retry layer only re-issues requests whose failure is retryable, so a connection-level
failure that is misclassified as fatal silently turns a recoverable error into a user-visible one.
-/
private def expectRetryable (err : Error) (what : String) : Async Unit := do
  unless err.isRetryable do
    throw <| IO.userError s!"{what}: expected a retryable error, got {ctorName err}"

private def assertStatusIs (response : Response Body.Stream) (expected : UInt16) : Async Unit := do
  unless response.line.status.toCode == expected do
    throw <| IO.userError s!"expected status {expected}, got {response.line.status.toCode}"

private def expectCompleted (completion : IO.Promise (Except Error Unit)) (what : String) : Async Unit := do
  match ← await completion.result! with
  | .ok () => pure ()
  | .error e =>
    throw <| IO.userError s!"{what}: completion reported {ctorName e} (retryable: {e.isRetryable}) after \
      the response was delivered in full"

private def expectCompletionFailed (completion : IO.Promise (Except Error Unit)) (what : String) : Async Unit := do
  match ← await completion.result! with
  | .ok () => throw <| IO.userError s!"{what}: completion promise reported success"
  | .error _ => pure ()

private def assertBodyIs (response : Response Body.Stream) (expected : String) : Async Unit := do
  let body : String ← response.body.readAll
  unless body == expected do
    throw <| IO.userError s!"expected body {expected.quote}, got {body.quote}"

/-- A body that stops short or is malformed must throw; it must never come back as a short read. -/
private def expectBodyThrows (response : Response Body.Stream) (what : String) : Async Unit := do
  let result ← try
      let body : String ← response.body.readAll
      pure (Except.ok body)
    catch _ => pure (Except.error ())
  if let .ok body := result then
    throw <| IO.userError s!"{what}: readAll returned {body.quote} instead of throwing"

private def shortTimeout : Timeout := ⟨200, by decide⟩

private def mediumTimeout : Timeout := ⟨500, by decide⟩

private def longTimeout : Timeout := ⟨30000, by decide⟩

/--
Timeouts long enough that none of them can fire inside a test, so an exchange that stops making
progress shows up as the test's own failure rather than as a plausible-looking timeout error.
-/
private def patientConfig : Client.Config :=
  { readTimeout := longTimeout, requestTimeout := longTimeout, keepAliveTimeout := longTimeout }

/-- A pool retires a connection by polling `isClosed`, so retirement has to become visible there. -/
private def expectRetiredWithin (connection : Connection) (ms : Nat) (what : String) : Async Unit := do
  for _ in [0:ms / 20] do
    if ← connection.isClosed then return
    sleep 20
  throw <| IO.userError s!"{what}: the connection was still open {ms}ms later"

private def settledWithin {α : Type} (task : Task α) (ms : Nat) : Async Bool := do
  for _ in [0:ms / 20] do
    if (← IO.getTaskState task) == .finished then return true
    sleep 20
  return false

/-! ### Happy path -/

#eval show IO _ from runWithTimeout "GET receives status, headers, and body" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient
  let promise ← sendInBackground connection (← mkRequest .get "/hello")

  let head ← readHead mockServer
  unless head.startsWith "GET /hello HTTP/1.1\r\n" do
    throw <| IO.userError s!"unexpected request line:\n{head.quote}"

  mockServer.send (rawResp "200 OK" #[("Content-Length", "5"), ("X-Trace", "abc")] "world")

  let (response, _) ← expectResponse promise
  assertStatusIs response 200
  match response.line.headers.get? (.mk "x-trace") with
  | none => throw <| IO.userError "response header X-Trace was not delivered"
  | some value =>
    unless value.value == "abc" do
      throw <| IO.userError s!"expected X-Trace \"abc\", got {value.value.quote}"

  let body : String ← response.body.readAll
  unless body == "world" do
    throw <| IO.userError s!"expected body \"world\", got {body.quote}"

#eval show IO _ from runWithTimeout "chunked response body is reassembled" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient
  let promise ← sendInBackground connection (← mkRequest .get "/chunked")

  discard <| readHead mockServer
  mockServer.send (rawResp "200 OK" #[("Transfer-Encoding", "chunked")] "")
  mockServer.send (Test.chunk "abc" ++ Test.chunk "def" ++ Test.chunkEnd).toUTF8

  let (response, _) ← expectResponse promise
  let body : String ← response.body.readAll
  unless body == "abcdef" do
    throw <| IO.userError s!"expected body \"abcdef\", got {body.quote}"

#eval show IO _ from runWithTimeout "completion promise resolves once the exchange finishes" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient
  let promise ← sendInBackground connection (← mkRequest .get "/done")

  discard <| readHead mockServer
  mockServer.send (rawResp "200 OK" #[("Content-Length", "2")] "hi")

  let (response, completion) ← expectResponse promise
  let _ : String ← response.body.readAll
  expectCompleted completion "plain exchange"

/-! ### Keep-alive reuse -/

#eval show IO _ from runWithTimeout "two sequential requests reuse one connection" 5000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient

  let first ← sendInBackground connection (← mkRequest .get "/one")
  let head1 ← readHead mockServer
  unless head1.startsWith "GET /one " do
    throw <| IO.userError s!"unexpected first request:\n{head1.quote}"
  mockServer.send (rawResp "200 OK" #[("Content-Length", "3")] "one")
  let (resp1, _) ← expectResponse first
  assertStatusIs resp1 200
  let body1 : String ← resp1.body.readAll
  unless body1 == "one" do
    throw <| IO.userError s!"expected \"one\", got {body1.quote}"

  let second ← sendInBackground connection (← mkRequest .get "/two")
  let head2 ← readHead mockServer
  unless head2.startsWith "GET /two " do
    throw <| IO.userError s!"second request did not reuse the connection:\n{head2.quote}"
  mockServer.send (rawResp "200 OK" #[("Content-Length", "3")] "two")
  let (resp2, _) ← expectResponse second
  assertStatusIs resp2 200
  let body2 : String ← resp2.body.readAll
  unless body2 == "two" do
    throw <| IO.userError s!"expected \"two\", got {body2.quote}"

/-! ### Timeouts and RequestOverrides -/

#eval show IO _ from runWithTimeout "connection-level requestTimeout aborts a silent server" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient { requestTimeout := shortTimeout }
  let promise ← sendInBackground connection (← mkRequest .get "/silent")

  discard <| readHead mockServer
  -- Never respond; the request deadline must fire.
  match ← expectError promise with
  | .timeout => pure ()
  | e => throw (IO.userError s!"expected .timeout, got {e}")

#eval show IO _ from runWithTimeout "per-request requestTimeout override aborts sooner than the config" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  -- Config allows 30s; the override must be what actually bounds this exchange.
  let connection ← mkConnection mockClient { requestTimeout := longTimeout }
  let promise ← sendInBackground connection (← mkRequest .get "/silent")
    { requestTimeout := some shortTimeout }

  discard <| readHead mockServer
  match ← expectError promise with
  | .timeout => pure ()
  | e => throw (IO.userError s!"expected .timeout, got {e}")

-- An override is scoped to its own request: each request's overrides are applied to the connection
-- config, never to the effective config the previous request left behind. If they compounded, the
-- second request would inherit the 30s override and blow this test's wall-clock limit rather than
-- timing out at the connection's own 200ms.
#eval show IO _ from runWithTimeout "an override does not leak into the next request" 5000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient { requestTimeout := shortTimeout }

  let first ← sendInBackground connection (← mkRequest .get "/one")
    { requestTimeout := some longTimeout }
  discard <| readHead mockServer
  mockServer.send (rawResp "200 OK" #[("Content-Length", "3")] "one")
  let (resp1, _) ← expectResponse first
  let _ : String ← resp1.body.readAll

  -- No override this time: the connection's own 200ms timeout must apply again.
  let second ← sendInBackground connection (← mkRequest .get "/two")
  discard <| readHead mockServer
  match ← expectError second with
  | .timeout => pure ()
  | e => throw (IO.userError s!"expected .timeout on the second request, got {e}")

-- `readTimeout` is the per-read idle bound, so it — not the much longer whole-exchange
-- `requestTimeout` — is what must fire when a server accepts a request and then goes silent.
#eval show IO _ from runWithTimeout "readTimeout bounds the wait for the response head" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient
    { readTimeout := shortTimeout, requestTimeout := longTimeout }
  let promise ← sendInBackground connection (← mkRequest .get "/silent")
  discard <| readHead mockServer
  match ← expectError promise with
  | .timeout => pure ()
  | e => throw (IO.userError s!"expected .timeout, got {e}")

-- Same bound on a reused keep-alive connection: `keepAliveTimeout` is long here, so only
-- `readTimeout` can bound the wait for the second response head.
#eval show IO _ from runWithTimeout "readTimeout bounds the second head on a reused connection" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient
    { readTimeout := shortTimeout, requestTimeout := longTimeout, keepAliveTimeout := longTimeout }
  let first ← sendInBackground connection (← mkRequest .get "/one")
  discard <| readHead mockServer
  mockServer.send (rawResp "200 OK" #[("Content-Length", "3")] "one")
  let (resp1, _) ← expectResponse first
  let _ : String ← resp1.body.readAll

  let second ← sendInBackground connection (← mkRequest .get "/two")
  discard <| readHead mockServer
  match ← expectError second with
  | .timeout => pure ()
  | e => throw (IO.userError s!"expected .timeout, got {e}")

/-! ### Response header limits -/

#eval show IO _ from runWithTimeout "maxResponseHeaders rejects a header-heavy response" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient { maxResponseHeaders := 3 }
  let promise ← sendInBackground connection (← mkRequest .get "/h")

  discard <| readHead mockServer
  let hdrs := (List.range 20).toArray.map (fun i => (s!"X-H{i}", "v"))
  mockServer.send (rawResp "200 OK" (hdrs.push ("Content-Length", "0")) "")

  match ← expectError promise with
  | .protocol _ => pure ()
  | e => throw (IO.userError s!"expected a protocol error, got {ctorName e}")

#eval show IO _ from runWithTimeout "maxHeaderValueSize rejects an oversized header value" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient { maxHeaderValueSize := 16 }
  let promise ← sendInBackground connection (← mkRequest .get "/h")

  discard <| readHead mockServer
  mockServer.send (rawResp "200 OK"
    #[("X-Big", String.ofList (List.replicate 400 'a')), ("Content-Length", "0")] "")

  match ← expectError promise with
  | .protocol _ => pure ()
  | e => throw (IO.userError s!"expected a protocol error, got {ctorName e}")

/-! ### Expect: 100-continue and informational responses -/

#eval show IO _ from runWithTimeout "the body waits for 100 Continue" 5000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient
  let request ← mkRequest .post "/submit" "payload-body" #[("Expect", "100-continue")]
  let promise ← sendInBackground connection request

  let head ← readHead mockServer
  if head.contains "payload-body" then
    throw <| IO.userError s!"body was sent before 100 Continue:\n{head.quote}"

  -- The head and a wrongly-released body go out in separate writes, so the read above can stop
  -- between them. Settle well inside the default `expectContinueTimeout` and probe the wire again.
  sleep 100
  if let some early ← mockServer.tryRecv? then
    throw <| IO.userError
      s!"body was sent before 100 Continue:\n{(String.fromUTF8! early).quote}"

  mockServer.send "HTTP/1.1 100 Continue\r\n\r\n".toUTF8
  discard <| readUntil mockServer "payload-body" head

  mockServer.send (rawResp "200 OK" #[("Content-Length", "2")] "ok")
  let (response, _) ← expectResponse promise
  assertStatusIs response 200

-- With no known body size the writer only flushes the head once body bytes (or producer EOF) are
-- buffered, but the body stays parked until `100 Continue` arrives. The head must go out anyway,
-- or neither side can proceed.
#eval show IO _ from runWithTimeout "a chunked request body with Expect: 100-continue sends its head" 6000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient
  let stream ← Body.mkStream
  let promise ← sendInBackground connection
    (mkStreamRequest "/chunked" stream #[("Expect", "100-continue")])

  -- Nothing has been produced yet, so reaching a complete head is the whole assertion here; the
  -- body-not-sent-early case is covered where the producer has already handed over bytes.
  let head ← readHead mockServer

  mockServer.send "HTTP/1.1 100 Continue\r\n\r\n".toUTF8
  stream.send { data := "payload-body".toUTF8, extensions := #[] }
  stream.close
  discard <| readUntil mockServer "payload-body" head

  mockServer.send (rawResp "200 OK" #[("Content-Length", "2")] "ok")
  let (response, _) ← expectResponse promise
  assertStatusIs response 200

-- A rejected expectation leaves the writer parked on a body that must never be sent. The machine
-- has to be told to abandon it, otherwise the writer never completes and the exchange only ends
-- when the request deadline expires.
#eval show IO _ from runWithTimeout "a 417 rejection completes the exchange without waiting for the deadline" 6000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient { requestTimeout := mediumTimeout }
  let request ← mkRequest .post "/submit" "payload-body" #[("Expect", "100-continue")]
  let promise ← sendInBackground connection request

  discard <| readHead mockServer
  mockServer.send (rawResp "417 Expectation Failed" #[("Content-Length", "0")] "")

  let (response, completion) ← expectResponse promise
  assertStatusIs response 417
  let _ : String ← response.body.readAll
  expectCompleted completion "417 rejection"

-- The head announced `Content-Length` for a body the rejection then abandons, so the peer is still
-- counting those bytes. Writing the next request onto the same connection would hand it to the
-- server as the body of this one (RFC 9112 §6.3), so the connection is retired instead and the
-- queued request comes back retryable for a pool to re-issue on a fresh one.
#eval show IO _ from runWithTimeout "a rejected expectation retires the connection" 6000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient { requestTimeout := mediumTimeout }
  let first ← sendInBackground connection
    (← mkRequest .post "/submit" "payload-body" #[("Expect", "100-continue")])

  discard <| readHead mockServer
  mockServer.send (rawResp "417 Expectation Failed" #[("Content-Length", "0")] "")
  let (resp1, _) ← expectResponse first
  assertStatusIs resp1 417
  let _ : String ← resp1.body.readAll
  expectRetiredWithin connection 1000 "417 with an unsent Content-Length body"

  let second ← sendInBackground connection (← mkRequest .post "/again" "second-body")
  expectRetryable (← expectError second) "queued behind a rejected expectation"

  -- Nothing may follow the truncated first request on the wire.
  connection.close
  let mut wire := ""
  repeat
    let some chunk ← mockServer.recv? | break
    wire := wire ++ String.fromUTF8! chunk
  if wire.contains "POST /again " then
    throw <| IO.userError
      s!"a second request was written after an abandoned Content-Length body:\n{wire.quote}"

-- An interim response and the final response arriving in one read leave the final response sitting
-- in the reader's buffer after the 1xx is consumed. The loop has to step again on that buffered
-- input rather than park waiting for socket bytes that will never come.
#eval show IO _ from runWithTimeout "a 103 coalesced with the final response in one segment" 6000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient
  let promise ← sendInBackground connection (← mkRequest .get "/hints")

  discard <| readHead mockServer
  mockServer.send ("HTTP/1.1 103 Early Hints\r\nLink: </s.css>; rel=preload\r\n\r\n".toUTF8
    ++ rawResp "200 OK" #[("Content-Length", "5")] "world")

  let (response, _) ← expectResponse promise
  assertStatusIs response 200
  let body : String ← response.body.readAll
  unless body == "world" do
    throw <| IO.userError s!"expected body \"world\", got {body.quote}"

/-! ### Exchanges that end without keep-alive -/

-- A response that disables keep-alive still finishes the exchange successfully. It leaves the
-- machine on the `.close` path instead of `.next`, and reporting a failure there would hand a
-- retryable error to a pool retry layer for a request the server already ran.
#eval show IO _ from runWithTimeout "Connection: close completes the exchange and retires the connection" 5000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient
  let promise ← sendInBackground connection (← mkRequest .post "/charge")

  discard <| readHead mockServer
  mockServer.send (rawResp "200 OK" #[("Content-Length", "6"), ("Connection", "close")] "billed")

  let (response, completion) ← expectResponse promise
  assertStatusIs response 200
  assertBodyIs response "billed"
  expectCompleted completion "Connection: close"
  expectRetiredWithin connection 1000 "Connection: close"

-- A request already queued behind an exchange the server ends with `Connection: close` never
-- reaches the wire, so it must come back retryable for a pool to re-issue on a fresh connection.
#eval show IO _ from runWithTimeout "a request queued behind a Connection: close exchange fails retryably" 6000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient
  let first ← sendInBackground connection (← mkRequest .get "/one")
  discard <| readHead mockServer
  let second ← sendInBackground connection (← mkRequest .get "/two")
  sleep 50

  mockServer.send (rawResp "200 OK" #[("Connection", "close"), ("Content-Length", "3")] "one")
  let (resp, _) ← expectResponse first
  let _ : String ← resp.body.readAll

  expectRetryable (← expectError second) "request queued behind Connection: close"

/-! ### Response body known size -/

#eval show IO _ from runWithTimeout "Content-Length sets the known response body size" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient
  let promise ← sendInBackground connection (← mkRequest .get "/sized")

  discard <| readHead mockServer
  mockServer.send (rawResp "200 OK" #[("Content-Length", "5")] "world")

  let (response, _) ← expectResponse promise
  match ← response.body.getKnownSize with
  | some (.fixed 5) => pure ()
  | other => throw <| IO.userError s!"expected some (.fixed 5), got {repr other}"

-- A response with no `Content-Length` and no `Transfer-Encoding` is read until EOF, so its length
-- is unknown. The empty-body reading of missing framing headers only holds for a *request* head.
#eval show IO _ from runWithTimeout "an EOF-framed response reports an unknown body size" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient
  let promise ← sendInBackground connection (← mkRequest .get "/unsized")

  discard <| readHead mockServer
  mockServer.send (rawResp "200 OK" #[] "streamed")

  let (response, completion) ← expectResponse promise
  match ← response.body.getKnownSize with
  | none => pure ()
  | other => throw <| IO.userError s!"expected none for an EOF-framed body, got {repr other}"

  mockServer.close
  assertBodyIs response "streamed"
  expectCompleted completion "EOF framing"

#eval show IO _ from runWithTimeout "a chunked response reports a chunked known size" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient
  let promise ← sendInBackground connection (← mkRequest .get "/chunked-size")

  discard <| readHead mockServer
  mockServer.send (rawResp "200 OK" #[("Transfer-Encoding", "chunked")] "")

  let (response, _) ← expectResponse promise
  match ← response.body.getKnownSize with
  | some .chunked => pure ()
  | other => throw <| IO.userError s!"expected some .chunked, got {repr other}"

  mockServer.send (Test.chunk "abc" ++ Test.chunkEnd).toUTF8
  let body : String ← response.body.readAll
  unless body == "abc" do
    throw <| IO.userError s!"expected \"abc\", got {body.quote}"

/-! ### Errors before and during a response -/

#eval show IO _ from runWithTimeout "server EOF before a response reports a retryable error" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient
  let promise ← sendInBackground connection (← mkRequest .get "/eof")

  discard <| readHead mockServer
  mockServer.close

  expectRetryable (← expectError promise) "server EOF before a response"

#eval show IO _ from runWithTimeout "a malformed status line reports a protocol error" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient
  let promise ← sendInBackground connection (← mkRequest .get "/garbage")

  discard <| readHead mockServer
  mockServer.send "not-an-http-response\r\n\r\n".toUTF8

  match ← expectError promise with
  | .protocol _ => pure ()
  | e => throw (IO.userError s!"expected a protocol error, got {ctorName e}")

-- The head was already handed to the caller, so a body that stops short must fail through the body
-- stream and the completion promise rather than through the response promise.
#eval show IO _ from runWithTimeout "server EOF mid Content-Length body fails the read and the completion" 6000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient
  let promise ← sendInBackground connection (← mkRequest .get "/short")

  discard <| readHead mockServer
  mockServer.send (rawResp "200 OK" #[("Content-Length", "10")] "abcd")
  let (response, completion) ← expectResponse promise
  assertStatusIs response 200
  mockServer.close

  expectBodyThrows response "truncated Content-Length body"
  expectCompletionFailed completion "truncated Content-Length body"

#eval show IO _ from runWithTimeout "a malformed chunk size mid-body fails the read and the completion" 6000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient
  let promise ← sendInBackground connection (← mkRequest .get "/chunked")

  discard <| readHead mockServer
  mockServer.send (rawResp "200 OK" #[("Transfer-Encoding", "chunked")] "")
  let (response, completion) ← expectResponse promise
  mockServer.send (Test.chunk "abc").toUTF8
  mockServer.send "zzzz\r\n".toUTF8

  expectBodyThrows response "malformed chunk size"

  match ← await completion.result! with
  | .ok () => throw (IO.userError "completion promise reported success after a protocol error")
  | .error (.protocol _) => pure ()
  | .error e => throw (IO.userError s!"expected .protocol on the completion promise, got {ctorName e}")

#eval show IO _ from runWithTimeout "a failing transport write reports .closed promptly" 6000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient
  -- Kill the client -> server direction so `Transport.sendAll` fails.
  mockServer.getRecvChan.close
  let promise ← sendInBackground connection (← mkRequest .get "/nowrite")
  match ← expectError promise with
  | .closed _ => pure ()
  | e => throw (IO.userError s!"expected .closed on a write failure, got {ctorName e}")

/-! ### Close and shutdown -/

#eval show IO _ from runWithTimeout "isClosed tracks close" 4000 <| Async.block do
  let (mockClient, _mockServer) ← Mock.new
  let connection ← mkConnection mockClient
  if ← connection.isClosed then
    throw (IO.userError "a fresh connection reported itself closed")
  connection.close
  unless ← connection.isClosed do
    throw (IO.userError "connection still open after close")

#eval show IO _ from runWithTimeout "close while waiting for 100 Continue resolves the caller" 6000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient
  let request ← mkRequest .post "/expect" "payload-body" #[("Expect", "100-continue")]
  let promise ← sendInBackground connection request
  discard <| readHead mockServer
  connection.close
  discard <| expectError promise

-- The caller is blocked in `readAll` when the connection goes away: it must be woken with an error
-- rather than handed the bytes received so far.
#eval show IO _ from runWithTimeout "close mid-body fails the read and the completion" 6000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient
  let promise ← sendInBackground connection (← mkRequest .get "/slow")

  discard <| readHead mockServer
  mockServer.send (rawResp "200 OK" #[("Content-Length", "10")] "ab")
  let (response, completion) ← expectResponse promise

  let readPromise ← IO.Promise.new
  background do
    let r ← try
        let s : String ← response.body.readAll
        pure (Except.ok s)
      catch e => pure (Except.error (toString e))
    discard <| readPromise.resolve r

  sleep 100
  connection.close

  match ← await readPromise.result! with
  | .ok s => throw (IO.userError s!"readAll returned {s.quote} after close instead of throwing")
  | .error _ => pure ()

  expectCompletionFailed completion "close mid-body"

#eval show IO _ from runWithTimeout "waitShutdown resolves after a protocol error" 6000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient
  let promise ← sendInBackground connection (← mkRequest .get "/garbage")
  discard <| readHead mockServer
  mockServer.send "not-an-http-response\r\n\r\n".toUTF8
  discard <| expectError promise
  connection.waitShutdown

#eval show IO _ from runWithTimeout "close is idempotent" 6000 <| Async.block do
  let (mockClient, _mockServer) ← Mock.new
  let connection ← mkConnection mockClient
  connection.close
  connection.close
  connection.close
  connection.waitShutdown

#eval show IO _ from runWithTimeout "close after a natural loop exit does not throw" 6000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient
  let promise ← sendInBackground connection (← mkRequest .get "/eof")
  discard <| readHead mockServer
  mockServer.close
  discard <| expectError promise
  connection.waitShutdown
  connection.close
  unless ← connection.isClosed do
    throw (IO.userError "connection not reported closed after a natural exit")

#eval show IO _ from runWithTimeout "a request sent after close fails" 4000 <| Async.block do
  let (mockClient, _mockServer) ← Mock.new
  let connection ← mkConnection mockClient
  connection.close
  connection.waitShutdown

  match ← connection.sendTracked (← mkRequest .get "/late") with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "a request was accepted after close")

#eval show IO _ from runWithTimeout "a send after the idle keep-alive timeout fails retryably" 6000 <| Async.block do
  let (mockClient, _mockServer) ← Mock.new
  let connection ← mkConnection mockClient { keepAliveTimeout := ⟨100, by decide⟩ }
  sleep 400
  match ← connection.sendTracked (← mkRequest .get "/late") with
  | .ok _ => throw (IO.userError "a request was accepted on an idle-timed-out connection")
  | .error e => expectRetryable e "send after the idle keep-alive timeout"

#eval show IO _ from runWithTimeout "a send after a server-initiated idle close fails retryably" 6000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient
  mockServer.close
  sleep 100
  match ← connection.sendTracked (← mkRequest .get "/late") with
  | .ok _ => throw (IO.userError "a request was accepted on a server-closed connection")
  | .error e => expectRetryable e "send after a server-initiated close"

/-! ### Queueing and concurrency -/

#eval show IO _ from runWithTimeout "every queued request resolves when the connection is closed" 6000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient

  let p1 ← sendInBackground connection (← mkRequest .get "/one")
  discard <| readHead mockServer
  let p2 ← sendInBackground connection (← mkRequest .get "/two")
  let p3 ← sendInBackground connection (← mkRequest .get "/three")
  let p4 ← sendInBackground connection (← mkRequest .get "/four")
  sleep 100

  connection.close

  discard <| expectError p1
  discard <| expectError p2
  discard <| expectError p3
  discard <| expectError p4

-- `close` can land at any point in `sendTracked`, including between queueing the request and
-- awaiting its promise; every interleaving must resolve rather than hang.
#eval show IO _ from runWithTimeout "close racing sendTracked always resolves" 8000 <| Async.block do
  for _ in [0:20] do
    let (mockClient, _mockServer) ← Mock.new
    let connection ← mkConnection mockClient
    let promise ← sendInBackground connection (← mkRequest .get "/race")
    connection.close
    discard <| await promise.result!

-- HTTP/1.1 serialises concurrent sends on one connection; each caller must still receive the
-- response to its own request.
#eval show IO _ from runWithTimeout "concurrent sends get their own responses" 8000 <| Async.block do
  for _ in [0:5] do
    let (mockClient, mockServer) ← Mock.new
    let connection ← mkConnection mockClient

    let pa ← sendInBackground connection (← mkRequest .get "/alpha")
    let pb ← sendInBackground connection (← mkRequest .get "/beta")

    let mut served : Array String := #[]
    for _ in [0:2] do
      let head ← readHead mockServer
      let path ←
        if head.startsWith "GET /alpha " then pure "alpha"
        else if head.startsWith "GET /beta " then pure "beta"
        else throw <| IO.userError s!"unrecognized request on the wire:\n{head.quote}"
      if served.contains path then
        throw <| IO.userError s!"request /{path} was sent twice"
      served := served.push path
      mockServer.send (rawResp "200 OK" #[("Content-Length", toString path.length)] path)
      let (resp, _) ← expectResponse (if path == "alpha" then pa else pb)
      let body : String ← resp.body.readAll
      unless body == path do
        throw <| IO.userError s!"caller for /{path} received body {body.quote}"

/-! ### Failures raised by a user-supplied request body -/

-- The loop calls `isClosed` and `getKnownSize` on a caller-provided `Body`. An exception from
-- either runs inside the background task, so it must be converted into a failed promise rather
-- than left to kill the loop with the caller still waiting.
#eval show IO _ from runWithTimeout "a request body whose isClosed throws does not hang the caller" 6000 <| Async.block do
  let (mockClient, _mockServer) ← Mock.new
  let connection ← mkConnection mockClient
  let base ← mkRequest .post "/boom"
  let request : Request Body.Any :=
    { base with body := { emptyAny with isClosed := throw (IO.userError "user body isClosed failed") } }
  let promise ← sendInBackground connection request
  discard <| expectError promise

#eval show IO _ from runWithTimeout "a request body whose getKnownSize throws does not hang the caller" 6000 <| Async.block do
  let (mockClient, _mockServer) ← Mock.new
  let connection ← mkConnection mockClient
  let base ← mkRequest .post "/boom2"
  let request : Request Body.Any :=
    { base with body := { emptyAny with getKnownSize := throw (IO.userError "user body getKnownSize failed") } }
  let promise ← sendInBackground connection request
  discard <| expectError promise

/-! ### Bodyless responses (RFC 9112 §6.3) -/

-- A HEAD response carries the `Content-Length` the equivalent GET would have, but no body. Framing
-- it like a GET response leaves the reader waiting for bytes that never arrive, and on a reused
-- connection it would swallow the next response as body.
#eval show IO _ from runWithTimeout "a HEAD response has no body and the connection is reused" 5000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient patientConfig
  let first ← sendInBackground connection (← mkRequest .head "/head")
  discard <| readHead mockServer
  mockServer.send (rawResp "200 OK" #[("Content-Length", "12")] "")
  let (resp1, _) ← expectResponse first
  assertStatusIs resp1 200
  assertBodyIs resp1 ""

  let second ← sendInBackground connection (← mkRequest .get "/after")
  let head2 ← readHead mockServer
  unless head2.startsWith "GET /after " do
    throw <| IO.userError s!"the connection was not reusable after a HEAD:\n{head2.quote}"
  mockServer.send (rawResp "200 OK" #[("Content-Length", "2")] "ok")
  let (resp2, _) ← expectResponse second
  assertBodyIs resp2 "ok"

#eval show IO _ from runWithTimeout "a HEAD response framed as chunked has no body" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient patientConfig
  let promise ← sendInBackground connection (← mkRequest .head "/head-chunked")
  discard <| readHead mockServer
  mockServer.send (rawResp "200 OK" #[("Transfer-Encoding", "chunked")] "")
  let (response, _) ← expectResponse promise
  assertBodyIs response ""

#eval show IO _ from runWithTimeout "a HEAD response with Connection: close completes" 5000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient patientConfig
  let promise ← sendInBackground connection (← mkRequest .head "/head-close")
  discard <| readHead mockServer
  mockServer.send (rawResp "200 OK" #[("Content-Length", "99"), ("Connection", "close")] "")
  let (response, completion) ← expectResponse promise
  assertBodyIs response ""
  expectCompleted completion "HEAD with Connection: close"

#eval show IO _ from runWithTimeout "204 No Content has no body and the connection is reused" 5000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient patientConfig
  let first ← sendInBackground connection (← mkRequest .delete "/gone")
  discard <| readHead mockServer
  mockServer.send (rawResp "204 No Content" #[] "")
  let (resp1, _) ← expectResponse first
  assertStatusIs resp1 204
  assertBodyIs resp1 ""

  let second ← sendInBackground connection (← mkRequest .get "/after")
  discard <| readHead mockServer
  mockServer.send (rawResp "200 OK" #[("Content-Length", "2")] "ok")
  let (resp2, _) ← expectResponse second
  assertBodyIs resp2 "ok"

-- RFC 9110 §15.4.5 lets a 304 carry the `Content-Length` of the cached representation, so the
-- header must not be read as a promise of body bytes.
#eval show IO _ from runWithTimeout "304 Not Modified with Content-Length has no body" 5000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient patientConfig
  let first ← sendInBackground connection (← mkRequest .get "/cached")
  discard <| readHead mockServer
  mockServer.send (rawResp "304 Not Modified" #[("Content-Length", "1234")] "")
  let (resp1, _) ← expectResponse first
  assertStatusIs resp1 304
  assertBodyIs resp1 ""

  let second ← sendInBackground connection (← mkRequest .get "/after")
  discard <| readHead mockServer
  mockServer.send (rawResp "200 OK" #[("Content-Length", "2")] "ok")
  let (resp2, _) ← expectResponse second
  assertBodyIs resp2 "ok"

/-! ### Response parsing -/

#eval show IO _ from runWithTimeout "an empty reason phrase is accepted" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient patientConfig
  let promise ← sendInBackground connection (← mkRequest .get "/noreason")
  discard <| readHead mockServer
  mockServer.send "HTTP/1.1 200 \r\nContent-Length: 2\r\n\r\nhi".toUTF8
  let (response, _) ← expectResponse promise
  assertStatusIs response 200
  assertBodyIs response "hi"

#eval show IO _ from runWithTimeout "an unknown 3-digit status code is delivered" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient patientConfig
  let promise ← sendInBackground connection (← mkRequest .get "/weird")
  discard <| readHead mockServer
  mockServer.send (rawResp "599 Whatever" #[("Content-Length", "2")] "hi")
  let (response, _) ← expectResponse promise
  assertStatusIs response 599
  assertBodyIs response "hi"

-- `Set-Cookie` is the one header that must never be merged, so a client that collapses repeats
-- silently drops sessions.
#eval show IO _ from runWithTimeout "repeated Set-Cookie headers are all preserved" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient patientConfig
  let promise ← sendInBackground connection (← mkRequest .get "/cookies")
  discard <| readHead mockServer
  mockServer.send (rawResp "200 OK"
    #[("Set-Cookie", "a=1"), ("Set-Cookie", "b=2"), ("Content-Length", "0")] "")
  let (response, _) ← expectResponse promise
  match response.line.headers.getAll? (.mk "set-cookie") with
  | some values =>
    unless values.size == 2 do
      throw <| IO.userError s!"expected 2 Set-Cookie headers, got {values.size}"
  | none => throw (IO.userError "Set-Cookie headers were dropped")

-- Nothing about a response may depend on how the peer chose to segment it.
#eval show IO _ from runWithTimeout "a response arriving one byte at a time is reassembled" 6000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient patientConfig
  let promise ← sendInBackground connection (← mkRequest .get "/dribble")
  discard <| readHead mockServer
  let raw := rawResp "200 OK" #[("Content-Length", "5")] "hello"
  for i in [0:raw.size] do
    mockServer.send (raw.extract i (i + 1))
  let (response, _) ← expectResponse promise
  assertBodyIs response "hello"

-- RFC 9110 §15.2: a client must be able to skip a 1xx it never asked for.
#eval show IO _ from runWithTimeout "an unsolicited 1xx before the final response is ignored" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient patientConfig
  let promise ← sendInBackground connection (← mkRequest .get "/unsolicited")
  discard <| readHead mockServer
  mockServer.send "HTTP/1.1 100 Continue\r\n\r\n".toUTF8
  mockServer.send (rawResp "200 OK" #[("Content-Length", "2")] "hi")
  let (response, _) ← expectResponse promise
  assertStatusIs response 200
  assertBodyIs response "hi"

#eval show IO _ from runWithTimeout "chunk extensions are ignored" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient patientConfig
  let promise ← sendInBackground connection (← mkRequest .get "/ext")
  discard <| readHead mockServer
  mockServer.send (rawResp "200 OK" #[("Transfer-Encoding", "chunked")] "")
  mockServer.send "3;name=value\r\nabc\r\n0\r\n\r\n".toUTF8
  let (response, _) ← expectResponse promise
  assertBodyIs response "abc"

#eval show IO _ from runWithTimeout "an uppercase hex chunk size is accepted" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient patientConfig
  let promise ← sendInBackground connection (← mkRequest .get "/hex")
  discard <| readHead mockServer
  mockServer.send (rawResp "200 OK" #[("Transfer-Encoding", "chunked")] "")
  mockServer.send "A\r\n0123456789\r\n0\r\n\r\n".toUTF8
  let (response, _) ← expectResponse promise
  assertBodyIs response "0123456789"

#eval show IO _ from runWithTimeout "trailers after the last chunk do not break reuse" 5000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient patientConfig
  let first ← sendInBackground connection (← mkRequest .get "/trailers")
  discard <| readHead mockServer
  mockServer.send (rawResp "200 OK" #[("Transfer-Encoding", "chunked")] "")
  mockServer.send "3\r\nabc\r\n0\r\nX-Checksum: deadbeef\r\n\r\n".toUTF8
  let (resp1, _) ← expectResponse first
  assertBodyIs resp1 "abc"

  let second ← sendInBackground connection (← mkRequest .get "/after")
  discard <| readHead mockServer
  mockServer.send (rawResp "200 OK" #[("Content-Length", "2")] "ok")
  let (resp2, _) ← expectResponse second
  assertBodyIs resp2 "ok"

#eval show IO _ from runWithTimeout "a chunked body cut short by EOF fails the read" 5000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient patientConfig
  let promise ← sendInBackground connection (← mkRequest .get "/truncated")
  discard <| readHead mockServer
  mockServer.send (rawResp "200 OK" #[("Transfer-Encoding", "chunked")] "")
  mockServer.send "3\r\nabc\r\n".toUTF8
  let (response, _) ← expectResponse promise
  mockServer.close
  expectBodyThrows response "chunked body cut short by EOF"

/-! ### Malformed framing is rejected, never guessed -/

#eval show IO _ from runWithTimeout "conflicting Content-Length headers are rejected" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient patientConfig
  let promise ← sendInBackground connection (← mkRequest .get "/smuggle")
  discard <| readHead mockServer
  mockServer.send "HTTP/1.1 200 OK\r\nContent-Length: 5\r\nContent-Length: 6\r\n\r\nhello".toUTF8
  match ← expectError promise with
  | .protocol _ => pure ()
  | e => throw (IO.userError s!"expected a protocol error, got {ctorName e}")

#eval show IO _ from runWithTimeout "Content-Length together with Transfer-Encoding is rejected" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient patientConfig
  let promise ← sendInBackground connection (← mkRequest .get "/smuggle2")
  discard <| readHead mockServer
  mockServer.send "HTTP/1.1 200 OK\r\nContent-Length: 5\r\nTransfer-Encoding: chunked\r\n\r\n0\r\n\r\n".toUTF8
  match ← expectError promise with
  | .protocol _ => pure ()
  | e => throw (IO.userError s!"expected a protocol error, got {ctorName e}")

-- RFC 9112 §5.1: whitespace between the field name and the colon must be rejected outright,
-- because proxies that tolerate it disagree about where the header ends.
#eval show IO _ from runWithTimeout "whitespace before a header colon is rejected" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient patientConfig
  let promise ← sendInBackground connection (← mkRequest .get "/badhdr")
  discard <| readHead mockServer
  mockServer.send "HTTP/1.1 200 OK\r\nX-Bad : v\r\nContent-Length: 0\r\n\r\n".toUTF8
  match ← expectError promise with
  | .protocol _ => pure ()
  | e => throw (IO.userError s!"expected a protocol error, got {ctorName e}")

#eval show IO _ from runWithTimeout "a non-numeric Content-Length is rejected" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient patientConfig
  let promise ← sendInBackground connection (← mkRequest .get "/badlen")
  discard <| readHead mockServer
  mockServer.send "HTTP/1.1 200 OK\r\nContent-Length: abc\r\n\r\n".toUTF8
  match ← expectError promise with
  | .protocol _ => pure ()
  | e => throw (IO.userError s!"expected a protocol error, got {ctorName e}")

#eval show IO _ from runWithTimeout "an unsupported HTTP version is rejected" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient patientConfig
  let promise ← sendInBackground connection (← mkRequest .get "/badver")
  discard <| readHead mockServer
  mockServer.send "HTTP/9.9 200 OK\r\nContent-Length: 0\r\n\r\n".toUTF8
  match ← expectError promise with
  | .protocol _ => pure ()
  | e => throw (IO.userError s!"expected a protocol error, got {ctorName e}")

/-! ### Keep-alive policy and retirement -/

#eval show IO _ from runWithTimeout "an HTTP/1.0 keep-alive response is reusable" 5000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient patientConfig
  let first ← sendInBackground connection (← mkRequest .get "/one")
  discard <| readHead mockServer
  mockServer.send "HTTP/1.0 200 OK\r\nContent-Length: 3\r\nConnection: keep-alive\r\n\r\none".toUTF8
  let (resp1, _) ← expectResponse first
  assertBodyIs resp1 "one"

  let second ← sendInBackground connection (← mkRequest .get "/two")
  let head2 ← readHead mockServer
  unless head2.startsWith "GET /two " do
    throw <| IO.userError s!"an HTTP/1.0 keep-alive connection was not reused:\n{head2.quote}"

#eval show IO _ from runWithTimeout "an HTTP/1.0 response without keep-alive retires the connection" 5000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient patientConfig
  let promise ← sendInBackground connection (← mkRequest .get "/one")
  discard <| readHead mockServer
  mockServer.send "HTTP/1.0 200 OK\r\nContent-Length: 3\r\n\r\none".toUTF8
  let (response, _) ← expectResponse promise
  assertBodyIs response "one"
  expectRetiredWithin connection 1000 "HTTP/1.0 without keep-alive"

#eval show IO _ from runWithTimeout "enableKeepAlive false sends Connection: close and retires" 5000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient { patientConfig with enableKeepAlive := false }
  let promise ← sendInBackground connection (← mkRequest .get "/once")
  let head ← readHead mockServer
  unless head.toLower.contains "connection: close" do
    throw <| IO.userError s!"keep-alive was disabled but the request did not say so:\n{head.quote}"
  mockServer.send (rawResp "200 OK" #[("Content-Length", "2")] "ok")
  let (response, _) ← expectResponse promise
  assertBodyIs response "ok"
  expectRetiredWithin connection 1000 "enableKeepAlive := false"

-- The request never reached the wire, so a pool must be free to re-issue it elsewhere.
#eval show IO _ from runWithTimeout "exceeding maxRequestsPerConnection fails retryably" 6000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient { patientConfig with maxRequestsPerConnection := 1 }
  let first ← sendInBackground connection (← mkRequest .get "/one")
  discard <| readHead mockServer
  mockServer.send (rawResp "200 OK" #[("Content-Length", "3")] "one")
  let (resp1, _) ← expectResponse first
  assertBodyIs resp1 "one"

  let second ← sendInBackground connection (← mkRequest .get "/two")
  expectRetryable (← expectError second) "past the request quota"

-- HTTP/1.1 has no way to skip an unread body, so the connection has to drain it itself before the
-- next request can go out.
--
-- Repeated, because `close` can land between the loop's own check that the response stream is still
-- open and the poll that registers the stream as a wake-up source. Land there and that poll carries
-- nothing but the cancellation selector: the body is drainable, the machine wants no input, and the
-- exchange never finishes.
#eval show IO _ from
  runWithTimeout "an unread response body does not block the next request" 120000 <| Async.block do
  for _ in [0:40] do
    let (mockClient, mockServer) ← Mock.new
    let connection ← mkConnection mockClient patientConfig
    let first ← sendInBackground connection (← mkRequest .get "/unread")
    discard <| readHead mockServer
    mockServer.send (rawResp "200 OK" #[("Content-Length", "5")] "hello")
    let (resp1, _) ← expectResponse first
    assertStatusIs resp1 200
    resp1.body.close

    let second ← sendInBackground connection (← mkRequest .get "/after")
    let head2 ← readHead mockServer
    unless head2.startsWith "GET /after " do
      throw <| IO.userError s!"the connection was not reusable after an unread body:\n{head2.quote}"
    mockServer.send (rawResp "200 OK" #[("Content-Length", "2")] "ok")
    let (resp2, _) ← expectResponse second
    assertBodyIs resp2 "ok"
    connection.close

#eval show IO _ from runWithTimeout "junk between responses is never delivered as a response" 5000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient patientConfig
  let first ← sendInBackground connection (← mkRequest .get "/one")
  discard <| readHead mockServer
  mockServer.send (rawResp "200 OK" #[("Content-Length", "3")] "one")
  mockServer.send "GARBAGE\r\n".toUTF8
  let (resp1, _) ← expectResponse first
  assertBodyIs resp1 "one"

  let second ← sendInBackground connection (← mkRequest .get "/two")
  match ← await second.result! with
  | .error _ => pure ()
  | .ok (resp, _) =>
    throw <| IO.userError s!"junk between responses surfaced as a response: {resp.line.status.toCode}"

/-! ### Request framing -/

#eval show IO _ from runWithTimeout "a POST body is framed with Content-Length" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient patientConfig
  discard <| sendInBackground connection (← mkRequest .post "/framed" "hello")
  let head ← readUntil mockServer "hello"
  unless head.toLower.contains "content-length: 5" do
    throw <| IO.userError s!"the POST body was not framed with Content-Length:\n{head.quote}"

#eval show IO _ from runWithTimeout "the request carries a default User-Agent" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient patientConfig
  discard <| sendInBackground connection (← mkRequest .get "/ua")
  let head ← readHead mockServer
  unless head.toLower.contains "user-agent:" do
    throw <| IO.userError s!"the request had no User-Agent header:\n{head.quote}"

#eval show IO _ from runWithTimeout "a caller-supplied Connection: close is sent" 5000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient patientConfig
  let promise ← sendInBackground connection (← mkRequest .get "/once" "" #[("Connection", "close")])
  let head ← readHead mockServer
  unless head.toLower.contains "connection: close" do
    throw <| IO.userError s!"the request did not carry Connection: close:\n{head.quote}"
  mockServer.send (rawResp "200 OK" #[("Content-Length", "2")] "ok")
  let (response, _) ← expectResponse promise
  assertBodyIs response "ok"

/-! ### Timeout scoping -/

-- The peer neither sends the rest of the body nor closes: only `readTimeout` can end this.
#eval show IO _ from runWithTimeout "readTimeout fires while the response body stalls" 5000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient { patientConfig with readTimeout := shortTimeout }
  let promise ← sendInBackground connection (← mkRequest .get "/stall")
  discard <| readHead mockServer
  mockServer.send (rawResp "200 OK" #[("Content-Length", "10")] "abcd")
  let (response, completion) ← expectResponse promise
  expectBodyThrows response "stalled response body"
  expectCompletionFailed completion "stalled response body"

-- `readTimeout` is a per-read bound, so a body that keeps trickling must never trip it.
#eval show IO _ from runWithTimeout "a slow but steady body does not trip readTimeout" 6000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient { patientConfig with readTimeout := ⟨400, by decide⟩ }
  let promise ← sendInBackground connection (← mkRequest .get "/slow")
  discard <| readHead mockServer
  mockServer.send (rawResp "200 OK" #[("Content-Length", "5")] "")
  let (response, _) ← expectResponse promise
  background do
    for c in ["a", "b", "c", "d", "e"] do
      sleep 150
      mockServer.send c.toUTF8
  assertBodyIs response "abcde"

#eval show IO _ from runWithTimeout "the request deadline covers a stalled upload" 5000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient { patientConfig with requestTimeout := ⟨400, by decide⟩ }
  let stream ← Body.mkStream
  let promise ← sendInBackground connection (mkStreamRequest "/stalled-upload" stream)
  stream.send { data := "start".toUTF8, extensions := #[] }
  discard <| readUntil mockServer "start"
  match ← expectError promise with
  | .timeout => pure ()
  | e => throw (IO.userError s!"expected .timeout on a stalled upload, got {ctorName e}")

-- An override must still be in force on a connection that has already served a request under the
-- connection-wide bound.
#eval show IO _ from runWithTimeout "a per-request timeout override applies on a reused connection" 6000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient { patientConfig with requestTimeout := ⟨400, by decide⟩ }
  let first ← sendInBackground connection (← mkRequest .get "/one")
  discard <| readHead mockServer
  mockServer.send (rawResp "200 OK" #[("Content-Length", "3")] "one")
  let (resp1, _) ← expectResponse first
  assertBodyIs resp1 "one"

  let second ← sendInBackground connection (← mkRequest .get "/two")
    { requestTimeout := some ⟨3000, by decide⟩ }
  discard <| readHead mockServer
  sleep 1200
  mockServer.send (rawResp "200 OK" #[("Content-Length", "3")] "two")
  let (resp2, _) ← expectResponse second
  assertBodyIs resp2 "two"

/-! ### Response body limits -/

#eval show IO _ from runWithTimeout "a body exactly at maxResponseBodySize is accepted" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient { patientConfig with maxResponseBodySize := some 5 }
  let promise ← sendInBackground connection (← mkRequest .get "/exact")
  discard <| readHead mockServer
  mockServer.send (rawResp "200 OK" #[("Content-Length", "5")] "hello")
  let (response, _) ← expectResponse promise
  assertBodyIs response "hello"

#eval show IO _ from runWithTimeout "the body limit is reported on the completion promise" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient { patientConfig with maxResponseBodySize := some 4 }
  let promise ← sendInBackground connection (← mkRequest .get "/big")
  discard <| readHead mockServer
  mockServer.send (rawResp "200 OK" #[("Content-Length", "20")] "aaaaaaaaaaaaaaaaaaaa")
  let (response, completion) ← expectResponse promise
  expectBodyThrows response "oversized body"
  match ← await completion.result! with
  | .error .bodyLimitExceeded => pure ()
  | .error e => throw (IO.userError s!"expected .bodyLimitExceeded on the completion, got {ctorName e}")
  | .ok () => throw (IO.userError "an oversized body reported a successful completion")

-- The counter belongs to one exchange: a connection that has already delivered several responses
-- must not accumulate them into the limit.
#eval show IO _ from runWithTimeout "the body limit is per response, not per connection" 6000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient { patientConfig with maxResponseBodySize := some 6 }
  for i in [0:3] do
    let promise ← sendInBackground connection (← mkRequest .get s!"/r{i}")
    discard <| readHead mockServer
    mockServer.send (rawResp "200 OK" #[("Content-Length", "5")] "hello")
    let (response, _) ← expectResponse promise
    assertBodyIs response "hello"

#eval show IO _ from runWithTimeout "a chunked body crossing the limit is rejected" 4000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient { patientConfig with maxResponseBodySize := some 4 }
  let promise ← sendInBackground connection (← mkRequest .get "/chunked-big")
  discard <| readHead mockServer
  mockServer.send (rawResp "200 OK" #[("Transfer-Encoding", "chunked")] "")
  mockServer.send (Test.chunk "abc" ++ Test.chunk "def" ++ Test.chunkEnd).toUTF8
  let (response, _) ← expectResponse promise
  expectBodyThrows response "chunked body over the limit"

/-! ### Exchanges that would otherwise stall -/

-- RFC 9110 §10.1.1: a server may ignore the expectation entirely, so the wait for `100 Continue`
-- is bounded by `expectContinueTimeout`. Without that bound the body is never sent and the whole
-- request dies at `requestTimeout` against an otherwise healthy server.
#eval show IO _ from runWithTimeout "a server that ignores Expect: 100-continue still gets the body" 6000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient
    { patientConfig with expectContinueTimeout := ⟨200, by decide⟩ }
  let promise ← sendInBackground connection
    (← mkRequest .post "/ignored" "payload-body" #[("Expect", "100-continue")])

  -- The peer never answers the expectation; the body must arrive anyway.
  let head ← readHead mockServer
  discard <| readUntil mockServer "payload-body" head
  mockServer.send (rawResp "200 OK" #[("Content-Length", "2")] "ok")
  let (response, _) ← expectResponse promise
  assertStatusIs response 200

-- Same fallback with a producer-driven body: the head is flushed up front (chunked framing), the
-- chunks sit parked until the deadline, and only then go out.
#eval show IO _ from runWithTimeout "a streamed body is sent when the server ignores Expect" 6000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient
    { patientConfig with expectContinueTimeout := ⟨200, by decide⟩ }
  let stream ← Body.mkStream
  let promise ← sendInBackground connection
    (mkStreamRequest "/ignored-stream" stream #[("Expect", "100-continue")])

  -- Produce from a background task: `Body.Stream` is a rendezvous channel, so a foreground `send`
  -- would itself block until the fallback releases the body and could never observe the parking.
  background do
    stream.send { data := "payload-body".toUTF8, extensions := #[] }
    stream.close

  let head ← readHead mockServer
  if head.contains "payload-body" then
    throw <| IO.userError s!"the body was sent before the expectation was resolved:\n{head.quote}"

  -- Well inside the 200ms fallback the produced chunk must still be parked.
  sleep 60
  if let some early ← mockServer.tryRecv? then
    throw <| IO.userError
      s!"the body was sent before the expectation was resolved:\n{(String.fromUTF8! early).quote}"

  discard <| readUntil mockServer "payload-body" head
  mockServer.send (rawResp "200 OK" #[("Content-Length", "2")] "ok")
  let (response, _) ← expectResponse promise
  assertStatusIs response 200

-- The fallback must stand down once the interim response arrives: a timer that still fires would
-- re-release an already-released body and the peer would see the payload twice.
#eval show IO _ from runWithTimeout "a prompt 100 Continue sends the body exactly once" 6000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient
    { patientConfig with expectContinueTimeout := ⟨200, by decide⟩ }
  let promise ← sendInBackground connection
    (← mkRequest .post "/prompt" "payload-body" #[("Expect", "100-continue")])

  let head ← readHead mockServer
  mockServer.send "HTTP/1.1 100 Continue\r\n\r\n".toUTF8
  let seen ← readUntil mockServer "payload-body" head
  -- Sit well past the fallback deadline before finishing the exchange.
  sleep 500
  mockServer.send (rawResp "200 OK" #[("Content-Length", "2")] "ok")
  let (response, _) ← expectResponse promise
  assertStatusIs response 200

  connection.close
  let mut wire := seen
  repeat
    let some chunk ← mockServer.recv? | break
    wire := wire ++ String.fromUTF8! chunk
  let occurrences := (wire.splitOn "payload-body").length - 1
  unless occurrences == 1 do
    throw <| IO.userError s!"the body was written {occurrences} times:\n{wire.quote}"

-- The peer answered in full and announced it will not read anything else, so the rest of the
-- upload is pointless: the exchange has to finish immediately instead of pumping a body nobody
-- reads until a timeout, and the producer has to be told to stop.
#eval show IO _ from runWithTimeout "a Connection: close response mid-upload ends the exchange at once" 6000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient patientConfig
  let stream ← Body.mkStream
  let promise ← sendInBackground connection (mkStreamRequest "/upload" stream)

  stream.send { data := "first-part".toUTF8, extensions := #[] }
  discard <| readUntil mockServer "first-part"

  mockServer.send (rawResp "413 Content Too Large" #[("Content-Length", "0"), ("Connection", "close")] "")
  let (response, completion) ← expectResponse promise
  assertStatusIs response 413
  assertBodyIs response ""

  unless ← settledWithin completion.result! 2000 do
    throw <| IO.userError "the completion promise stalled after the peer closed the exchange"
  expectCompleted completion "Connection: close mid-upload"

  let mut closed := false
  for _ in [0:50] do
    if ← Body.isClosed stream then
      closed := true
      break
    sleep 20
  unless closed do
    throw (IO.userError "the request body stream was left open after the exchange ended")

-- An abandoned upload is truncated and the socket is dropped, which is what Go's transport and
-- curl do in this situation. Writing the terminating zero chunk instead would tell the peer (or an
-- intermediary) that a body it never received was complete.
#eval show IO _ from runWithTimeout "an abandoned upload is truncated, not framed as complete" 6000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient patientConfig
  let stream ← Body.mkStream
  let promise ← sendInBackground connection (mkStreamRequest "/upload" stream)

  stream.send { data := "first-part".toUTF8, extensions := #[] }
  let seen ← readUntil mockServer "first-part"

  mockServer.send (rawResp "413 Content Too Large" #[("Content-Length", "0"), ("Connection", "close")] "")
  let (response, completion) ← expectResponse promise
  assertStatusIs response 413
  expectCompleted completion "abandoned upload"

  -- The client must close the transport rather than leave a half-written request hanging.
  let mut wire := seen
  repeat
    let some chunk ← mockServer.recv? | break
    wire := wire ++ String.fromUTF8! chunk
  if wire.endsWith "0\r\n\r\n" then
    throw <| IO.userError s!"the abandoned body was framed as a complete chunked body:\n{wire.quote}"

end ConnectionTests
