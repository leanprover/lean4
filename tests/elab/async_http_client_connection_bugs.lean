module

import Std.Http.Test.Helpers

open Std.Async
open Std Http Internal
open Test.ClientHelpers

/-!
Failing tests for two defects in `Std.Http.Client.Connection`.

1. `sendTracked` throws a raw `IO.Error` instead of returning `Except.error` when the body of an
   authentication challenge fails while `captureIntermediateBody` is reading it for a possible
   authenticated retry.
2. A request body producer that fails while the connection loop is parked in `pollNextEvent` is
   reported as a *retryable* `.closed`, losing the producer's own error, even though the peer has
   already been handed a partial request body.
-/

namespace ConnectionBugTests

open Std.Http.Client

private def mkConnection (mockClient : Mock.Client) (config : Client.Config := {}) : Async Connection :=
  Connection.new mockClient (origin "example.com") config

private def mkRequest (method : Method) (path : String) (body : String := "") :
    Async (Request Body.Any) := do
  let request ← Request.new |>.method method |>.uri! path |>.header! "Host" "example.com"
    |>.text body
  pure { request with }

/-- Read from the peer until everything seen so far contains `needle`. -/
private def readUntil (mockServer : Mock.Server) (needle : String) (seen : String := "") :
    Async String := do
  let mut acc := seen
  repeat
    if acc.contains needle then break
    let some chunk ← mockServer.recv?
      | throw (IO.userError s!"connection closed before {needle.quote} arrived; got {acc.quote}")
    acc := acc ++ String.fromUTF8! chunk
  pure acc

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
The outcome of one `sendTracked`, keeping the distinction the typed API is supposed to make: a
returned `Except Error` on one side, a thrown `IO.Error` on the other.
-/
private inductive Outcome where
  | response (status : UInt16)
  | failed (error : Error)
  | threw (error : IO.Error)
deriving Nonempty

/--
Runs `sendTracked` off the test's own task so the test can act as the peer while the exchange is in
flight, recording whether it returned or threw.
-/
private def sendInBackground (connection : Connection) (request : Request Body.Any) :
    Async (IO.Promise Outcome) := do
  let promise : IO.Promise Outcome ← IO.Promise.new
  background do
    let outcome ←
      try
        match ← connection.sendTracked request with
        | .ok ⟨response, _⟩ => pure (Outcome.response response.line.status.toCode)
        | .error e => pure (Outcome.failed e)
      catch e => pure (Outcome.threw e)
    discard <| promise.resolve outcome
  pure promise

private def constAuthConfig : Client.Config :=
  { authenticator := some (.const (.mk "Bearer letmein")) }

/-- A connection whose exchange has ended must also let its background loop go. -/
private def expectShutdownWithin (connection : Connection) (ms : Nat) (what : String) :
    Async Unit := do
  for _ in [0:ms / 20] do
    if (← IO.getTaskState connection.shutdown.result?) == .finished then return
    sleep 20
  throw <| IO.userError s!"{what}: the background loop was still running {ms}ms after the \
    exchange failed"

/--
Asserts that the exchange reported a failure the caller can act on. `expected` names the `Error` the
connection loop had already built for this failure before `sendTracked` reached it, so a fix has no
latitude about which one comes back.
-/
private def expectTypedError (outcome : Outcome) (expected : Error) (what : String) : Async Unit := do
  match outcome with
  | .threw e =>
    throw <| IO.userError s!"{what}: sendTracked threw {(toString e).quote} instead of returning \
      {ctorName expected}; a caller that classifies failures with `Error.isRetryable` never sees \
      this one"
  | .response status =>
    throw <| IO.userError s!"{what}: expected {ctorName expected}, got a {status} response"
  | .failed e =>
    unless ctorName e == ctorName expected do
      throw <| IO.userError s!"{what}: expected {ctorName expected}, got {ctorName e}"

/--
A `401` that keeps the connection alive and promises more body than the peer will ever send, so the
challenge body fails underneath the client while it is being captured for the retry.
-/
private def truncatedChallenge401 : ByteArray :=
  rawResp "401 Unauthorized"
    #[("WWW-Authenticate", "Basic realm=\"x\""), ("Content-Length", "100")] "deny"

/-! ### `sendTracked` must report a failed challenge body as a typed error -/

-- `send`'s documentation names the contract: `sendTracked` reports failures "as a typed `Error`
-- instead of a thrown exception". A caller above this layer classifies with `Error.isRetryable`,
-- and an exception carries no classification at all, so a thrown failure is not a cosmetic
-- difference — it is a failure the pool cannot decide about.
--
-- The identical truncation on a response the client does *not* answer itself is reported the typed
-- way (the next test), so nothing about the peer's behaviour makes this case unreportable.
#eval show IO _ from
  runWithTimeout "a challenge body cut short is reported as a typed error" 6000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient constAuthConfig
  let promise ← sendInBackground connection (← mkRequest .get "/secret")

  discard <| readUntil mockServer "\r\n\r\n"
  mockServer.send truncatedChallenge401
  -- Let the four body bytes land before the peer disappears, so the failure happens inside the
  -- capture rather than before it starts.
  sleep 100
  mockServer.getSendChan.close

  expectTypedError (← await promise.result!) (.closed "connection closed") "a truncated challenge body"

-- The same peer behaviour without an authenticator configured: the client hands the challenge
-- straight to the caller, so the body is never captured. This is the baseline the test above is
-- measured against — the response arrives, and the truncation is reported on the body and on the
-- completion promise rather than thrown out of `sendTracked`.
#eval show IO _ from
  runWithTimeout "a truncated body with no authenticator is reported the typed way" 6000 <|
    Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient
  let promise ← sendInBackground connection (← mkRequest .get "/secret")

  discard <| readUntil mockServer "\r\n\r\n"
  mockServer.send truncatedChallenge401
  sleep 100
  mockServer.getSendChan.close

  match ← await promise.result! with
  | .response _ | .failed _ => pure ()
  | .threw e =>
    throw <| IO.userError s!"sendTracked threw {(toString e).quote} on a plain truncated response"

-- The same defect reached by a deadline rather than by an EOF: the peer opens a chunked challenge
-- body and stops, and the request deadline closes the caller's stream underneath the capture.
#eval show IO _ from
  runWithTimeout "a challenge body that outlives the deadline is reported as a typed error" 8000 <|
    Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient
    { constAuthConfig with
        readTimeout := ⟨300, by decide⟩
        requestTimeout := ⟨2000, by decide⟩ }
  let promise ← sendInBackground connection (← mkRequest .get "/secret")

  discard <| readUntil mockServer "\r\n\r\n"
  mockServer.send (rawResp "401 Unauthorized"
    #[("WWW-Authenticate", "Basic realm=\"x\""), ("Transfer-Encoding", "chunked")] "")
  -- One chunk and then silence: the body never reaches its terminator.
  mockServer.send (Test.chunk "deny").toUTF8

  expectTypedError (← await promise.result!) .timeout "a stalled challenge body"

-- And once more through `maxResponseBodySize`: the limit is a typed `Error` everywhere else, but a
-- challenge body that trips it is thrown instead.
#eval show IO _ from
  runWithTimeout "a challenge body over maxResponseBodySize is reported as a typed error" 6000 <|
    Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← mkConnection mockClient
    { constAuthConfig with maxResponseBodySize := some 2 }
  let promise ← sendInBackground connection (← mkRequest .get "/secret")

  discard <| readUntil mockServer "\r\n\r\n"
  mockServer.send (rawResp "401 Unauthorized"
    #[("WWW-Authenticate", "Basic realm=\"x\""), ("Content-Length", "8")] "denydeny")

  expectTypedError (← await promise.result!) .bodyLimitExceeded "an oversized challenge body"

/-! ### A failed request-body producer must not look retryable -/

/--
A chunked request whose producer hands over one chunk and then fails. `gate` holds the failure back
until the test has seen that chunk on the wire, so the connection loop is parked in `pollNextEvent`
on the body's `recvSelector` when `Body.stream` closes the body with the producer's error.

`closeFinishedBodies` documents the intended handling of exactly this failure: a body that raises
"ends the message where it stands and fails the exchange instead", because "framing a failed body
would hand the peer a truncated request that looks complete". Taken through the poll instead, the
raise reaches `pollNextEvent`'s blanket `catch _ => pure .close`, which turns it into an ordinary
transport shutdown.
-/
private def failingBodyRequest (gate : IO.Promise Unit) : Async (Request Body.Any) := do
  let stream ← Body.stream fun s => do
    s.send (Chunk.ofByteArray "abc".toUTF8)
    -- `result?`, not `result!`: a gate the test drops on its way out of a failed assertion parks a
    -- `result!` producer here for good, and the exchange it holds open outlives the failure that
    -- should have been reported.
    discard <| await gate.result?
    throw (IO.userError "producer exploded")
  pure { (Request.new |>.method .post |>.uri! "/upload" |>.header! "Host" "example.com"
    |>.body stream) with }

-- The peer has already been handed `3\r\nabc\r\n` with no terminating chunk when the producer
-- fails, so the request is neither complete nor absent: replaying it would send that body twice. A
-- retryable error is a licence to replay — `Error.isRetryable` promises the request "provably
-- produced no application-level effect" — so classifying this failure as retryable is what makes
-- it a defect, independently of which error is reported.
--
-- The same producer failure observed by `closeFinishedBodies` instead of by the poll is reported
-- as a non-retryable `.io` carrying the producer's own message (the next test).
#eval show IO _ from
  runWithTimeout "a request body producer that fails is not retryable" 8000 <| Async.block do
  for _ in [0:5] do
    let (mockClient, mockServer) ← Mock.new
    let connection ← mkConnection mockClient
    let gate ← IO.Promise.new
    let promise ← sendInBackground connection (← failingBodyRequest gate)

    -- The whole chunk is named, not just its data: `readUntil` stops at the first byte that
    -- completes the needle, so waiting for `abc` alone can return before the CRLF that closes the
    -- chunk has been read, and the framing assertion below then races the writer's last write.
    let onWire ← readUntil mockServer "3\r\nabc\r\n"

    -- Released before anything below can throw: the producer is parked on this promise, and a gate
    -- dropped unresolved leaves it parked for good, so a failing assertion would hang the test
    -- instead of reporting itself.
    discard <| gate.resolve ()

    if onWire.contains "0\r\n\r\n" then
      throw <| IO.userError s!"expected a partial chunked body on the wire, got {onWire.quote}"

    match ← await promise.result! with
    | .response status =>
      throw <| IO.userError s!"expected a failure, got a {status} response"
    | .threw e =>
      throw <| IO.userError
        s!"sendTracked threw {(toString e).quote} instead of returning a typed Error"
    | .failed e =>
      if e.isRetryable then
        throw <| IO.userError s!"a request whose body producer failed after {onWire.quote} was on \
          the wire is reported as {ctorName e}, which `Error.isRetryable` accepts: a retry layer \
          will replay the request and send the body a second time"
      -- Named rather than merely non-retryable: `.timeout` is non-retryable too, so an exchange
      -- that stalled instead of reporting the producer's failure would satisfy the check above
      -- without the behaviour under test existing at all.
      unless (ctorName e).startsWith ".io" ∧ (ctorName e).contains "producer exploded" do
        throw <| IO.userError s!"expected the producer's own error, got {ctorName e}"

    -- The loop closes the bodies it owns as it winds down. The body that raised is not one of
    -- them: it closed itself, and its lock is held by the producer that raised, which
    -- `Mutex.atomically` is not reentrant across — so reaching for it here wedges the loop.
    expectShutdownWithin connection 2000 "a failed request body producer"

-- The baseline: a body that raises reached through `closeFinishedBodies` rather than through the
-- poll. It is a hand-built `Body.Any` rather than a real producer, because a real `Body.stream`
-- always fails while the loop is parked; what it models is a body already closed with a terminal
-- error, which is the state `closeWithError` leaves behind either way. It is reported as `.io`
-- carrying the producer's own message, and `isRetryable` rejects it — so nothing about a failing
-- body makes that classification unavailable above.
--
-- This body reports closed on the loop's first iteration, so the head is never even flushed and
-- the peer receives nothing at all. Read against the test above, the two classifications are
-- backwards with respect to what reached the wire: the request that wrote nothing is
-- non-retryable, the request that wrote a partial body is retryable.
#eval show IO _ from
  runWithTimeout "a body that raises outside the poll is reported as a non-retryable .io" 6000 <|
    Async.block do
  let (mockClient, _mockServer) ← Mock.new
  let connection ← mkConnection mockClient
  let base ← mkRequest .post "/upload"
  let emptyAny : Body.Any := Body.Any.ofBody ({} : Body.Empty)
  let request : Request Body.Any :=
    { base with body :=
        { emptyAny with
            isClosed := pure true
            getKnownSize := pure none
            tryRecv := throw (IO.userError "producer exploded") } }
  let promise ← sendInBackground connection request

  match ← await promise.result! with
  | .response status => throw <| IO.userError s!"expected a failure, got a {status} response"
  | .threw e => throw <| IO.userError s!"sendTracked threw {(toString e).quote}"
  | .failed e =>
    if e.isRetryable then
      throw <| IO.userError s!"a raising request body is reported as the retryable {ctorName e}"
    unless (ctorName e).startsWith ".io" ∧ (ctorName e).contains "producer exploded" do
      throw <| IO.userError s!"expected the producer's own error, got {ctorName e}"

end ConnectionBugTests
