module

import Std.Http.Test.Helpers

/-!
Regression tests for HTTP client connection lifecycle failures found while reviewing #14547,
involving response backpressure, request-body producer errors, and the bounds that apply to each
wait the connection loop parks on.
-/

open Std.Async
open Std Http Internal
open Std.Http.Client
open Std.Http.Internal.Test.ClientHelpers

namespace ClientConnectionLifecycleTests

private def mkConnection (client : Mock.Client) (config : Client.Config) : Async Connection :=
  Connection.new client (origin "example.com") config

private def mkRequest (path : String)
    (body : Body.Any := Body.Any.ofBody ({} : Body.Empty)) : Request Body.Any :=
  { (Request.new |>.method .post |>.uri! path |>.header! "Host" "example.com").body body with }

private def sendInBackground (connection : Connection) (request : Request Body.Any) :
    Async (IO.Promise (Except Error TrackedResponse)) := do
  let promise ← IO.Promise.new
  background do
    promise.resolve (← connection.sendTracked request)
  pure promise

private def expectResponse
    (promise : IO.Promise (Except Error TrackedResponse)) :
    Async TrackedResponse := do
  match ← await promise.result! with
  | .ok result => pure result
  | .error e => throw (IO.userError s!"expected a response, got {e}")

private def readHead (peer : Mock.Server) : Async String := do
  let mut bytes := ByteArray.empty
  repeat
    if (String.fromUTF8! bytes).contains "\r\n\r\n" then break
    let some chunk ← peer.recv?
      | throw (IO.userError "connection closed before the request head")
    bytes := bytes ++ chunk
  pure (String.fromUTF8! bytes)

private def errorConstructor : Error → String
  | .connect _ => ".connect"
  | .timeout => ".timeout"
  | .closed _ => ".closed"
  | .protocol _ => ".protocol"
  | .bodyLimitExceeded => ".bodyLimitExceeded"
  | .invalidRequest _ => ".invalidRequest"
  | .io _ => ".io"

/-- Waits up to `ms` for the exchange to settle, then reports how it ended. -/
private def settleWithin (completion : IO.Promise (Except Error Unit)) (ms : Nat) (what : String) :
    Async (Except Error Unit) := do
  for _ in [0:ms / 20] do
    if (← IO.getTaskState completion.result?) == .finished then return (← await completion.result!)
    sleep 20
  throw (IO.userError s!"{what}: the exchange had not settled {ms}ms later")

/-- Asserts that the exchange ended on its deadline rather than on some other failure. -/
private def expectTimedOut (completion : IO.Promise (Except Error Unit)) (ms : Nat) (what : String) :
    Async Unit := do
  match ← settleWithin completion ms what with
  | .error .timeout => pure ()
  | .error e => throw (IO.userError s!"{what}: expected .timeout, got {errorConstructor e}")
  | .ok () => throw (IO.userError s!"{what}: the exchange reported success")

/-!
The read timeout bounds waits for network data, not time spent waiting for the caller to consume
body bytes that have already arrived.
-/
#eval show IO _ from runWithTimeout "buffered response body survives readTimeout" 3000 <|
    Async.block do
  let (client, peer) ← Mock.new
  let connection ← mkConnection client
    ({ readTimeout := ⟨100, by decide⟩, requestTimeout := ⟨2000, by decide⟩,
       keepAliveTimeout := ⟨2000, by decide⟩ } : Client.Config)
  try
    let result ← sendInBackground connection (mkRequest "/buffered")
    discard <| readHead peer
    peer.send (rawResp "200 OK" #[("Content-Length", "2")] "ok")
    let ⟨response, _⟩ ← expectResponse result

    sleep 250

    let body : String ← response.body.readAll
    unless body == "ok" do
      throw (IO.userError s!"expected buffered body \"ok\", got {body.quote}")
  finally
    connection.close

/-!
An error raised by a request-body producer is an `.io` failure. It must not be collapsed into the
retryable `.closed` constructor merely because it arrives through a selector.
-/
#eval show IO _ from runWithTimeout "request body selector preserves producer error" 3000 <|
    Async.block do
  let (client, peer) ← Mock.new
  let connection ← mkConnection client
    ({ readTimeout := ⟨2000, by decide⟩, requestTimeout := ⟨2000, by decide⟩ } : Client.Config)
  try
    let stream ← Body.mkStream
    stream.setKnownSize (some (.fixed 1))
    let result ← sendInBackground connection
      (mkRequest "/body-error" (Body.Any.ofBody stream))
    discard <| readHead peer

    -- Let the connection register the request-body selector before failing the producer.
    sleep 50
    stream.closeWithError (IO.userError "producer failed")

    match ← await result.result! with
    | .error (.io _) => pure ()
    | .error e =>
      throw (IO.userError s!"expected .io, got {errorConstructor e}")
    | .ok _ =>
      throw (IO.userError "expected the request-body failure to reject the request")
  finally
    connection.close

/-!
The other side of that bound: with the peer silent and the body unread, the exchange is bounded by
`requestTimeout`, and that bound has to arrive.
-/
#eval show IO _ from runWithTimeout "an unread response body is bounded by requestTimeout" 6000 <|
    Async.block do
  let (client, peer) ← Mock.new
  let connection ← mkConnection client
    ({ readTimeout := ⟨200, by decide⟩, requestTimeout := ⟨2000, by decide⟩,
       keepAliveTimeout := ⟨30000, by decide⟩ } : Client.Config)
  try
    let result ← sendInBackground connection (mkRequest "/unread")
    discard <| readHead peer
    peer.send (rawResp "200 OK" #[("Content-Length", "10")] "abcd")
    let ⟨_response, completion⟩ ← expectResponse result

    -- Well clear of `readTimeout` and well short of `requestTimeout`, so neither a slow machine
    -- nor a fast one can decide this.
    sleep 600
    if (← IO.getTaskState completion.result?) == .finished then
      throw (IO.userError "the exchange ended while the caller still held an unread body: the \
        socket bound fired on a wait that was not the peer's")

    expectTimedOut completion 3000 "an unread response body"
  finally
    connection.close

/-!
The bound stands down only while bytes for the caller are actually in hand: a caller that walks away
from its stream hands the body back to the loop, whose wait is the peer's again.
-/
#eval show IO _ from runWithTimeout "an abandoned response body re-arms readTimeout" 6000 <|
    Async.block do
  let (client, peer) ← Mock.new
  let connection ← mkConnection client
    ({ readTimeout := ⟨200, by decide⟩, requestTimeout := ⟨30000, by decide⟩,
       keepAliveTimeout := ⟨30000, by decide⟩ } : Client.Config)
  try
    let result ← sendInBackground connection (mkRequest "/abandoned")
    discard <| readHead peer
    peer.send (rawResp "200 OK" #[("Content-Length", "10")] "abcd")
    let ⟨response, completion⟩ ← expectResponse result

    response.body.close

    expectTimedOut completion 3000 "an abandoned response body"
  finally
    connection.close

/-!
A caller that consumed everything buffered is waiting on the peer again, even though the reader is
still on the body: the pull that empties the buffer re-arms the bound.
-/
#eval show IO _ from runWithTimeout "a drained response body re-arms readTimeout" 6000 <|
    Async.block do
  let (client, peer) ← Mock.new
  let connection ← mkConnection client
    ({ readTimeout := ⟨300, by decide⟩, requestTimeout := ⟨30000, by decide⟩,
       keepAliveTimeout := ⟨30000, by decide⟩ } : Client.Config)
  try
    let result ← sendInBackground connection (mkRequest "/drained")
    discard <| readHead peer
    peer.send (rawResp "200 OK" #[("Transfer-Encoding", "chunked")] "")
    peer.send (Test.chunk "abc").toUTF8
    let ⟨response, completion⟩ ← expectResponse result

    let some chunk ← response.body.recv
      | throw (IO.userError "expected the chunk the peer sent")
    unless String.fromUTF8! chunk.data == "abc" do
      throw (IO.userError s!"expected chunk \"abc\", got {(String.fromUTF8! chunk.data).quote}")

    expectTimedOut completion 3000 "a drained response body"
  finally
    connection.close

/-!
The same bound seen from the request side: a peer that is receiving a request is silent by
definition, so a caller producing its body in slow bursts must not have its own upload timed out.
-/
#eval show IO _ from runWithTimeout "a slow request body does not trip readTimeout" 8000 <|
    Async.block do
  let (client, peer) ← Mock.new
  let connection ← mkConnection client
    ({ readTimeout := ⟨200, by decide⟩, requestTimeout := ⟨6000, by decide⟩,
       keepAliveTimeout := ⟨6000, by decide⟩ } : Client.Config)
  try
    let stream ← Body.mkStream
    stream.setKnownSize (some (.fixed 6))
    let result ← sendInBackground connection
      (mkRequest "/slow-upload" (Body.Any.ofBody stream))

    -- The peer answers the moment the whole request has arrived, so no silence of its own can
    -- account for a timeout here: only the caller's own pace is left to blame it on.
    background do
      try
        let mut seen := ByteArray.empty
        repeat
          if (String.fromUTF8! seen).contains "abcdef" then break
          let some chunk ← peer.recv? | break
          seen := seen ++ chunk
        peer.send (rawResp "200 OK" #[("Content-Length", "2")] "ok")
      catch _ => pure ()

    -- Swallowed so the exchange is what reports a failure: a producer raising because the
    -- connection went away under it would otherwise mask what went wrong.
    for piece in ["abc", "def"] do
      sleep 400
      try stream.send (Chunk.ofByteArray piece.toUTF8) catch _ => break
    try stream.close catch _ => pure ()

    let ⟨response, _⟩ ← expectResponse result
    unless response.line.status.toCode == 200 do
      throw (IO.userError s!"expected 200, got {response.line.status.toCode}")
  finally
    connection.close

/-!
That stand-down is scoped to the upload: with the request body on the wire the loop is waiting on
the peer again, and `readTimeout` — not the far longer `requestTimeout` — is what ends the wait.
-/
#eval show IO _ from runWithTimeout "readTimeout re-arms once the request body is sent" 5000 <|
    Async.block do
  let (client, peer) ← Mock.new
  let connection ← mkConnection client
    ({ readTimeout := ⟨200, by decide⟩, requestTimeout := ⟨30000, by decide⟩,
       keepAliveTimeout := ⟨30000, by decide⟩ } : Client.Config)
  try
    let stream ← Body.mkStream
    stream.setKnownSize (some (.fixed 3))
    let result ← sendInBackground connection
      (mkRequest "/finished-upload" (Body.Any.ofBody stream))
    discard <| readHead peer
    stream.send (Chunk.ofByteArray "abc".toUTF8)
    stream.close

    match ← await result.result! with
    | .error .timeout => pure ()
    | .error e => throw (IO.userError s!"expected .timeout, got {errorConstructor e}")
    | .ok _ => throw (IO.userError "the exchange reported success")
  finally
    connection.close

/--
A body large enough that pulling it takes longer than the timer the read below is raced against, so
the consumer is reliably gone by the time the loop reaches the hand-over.
-/
private def slowToPull : ByteArray := Id.run do
  let mut bytes := ("x".pushn 'y' 1023).toUTF8
  for _ in [0:14] do
    bytes := bytes ++ bytes
  return bytes

/-!
`.bodyInterest true` reports only that a consumer was registered when the selector fired. A consumer
racing that read against something else can lose and be gone before the loop hands the chunk over,
and the hand-over parks outside the poll, where neither the exchange deadline nor `close` reaches
it. However the race falls, the exchange has to end.

A machine fast enough for the read to win the race leaves nothing here to catch, which makes this
test weaker rather than flaky.
-/
#eval show IO _ from runWithTimeout "a hand-over the consumer walked away from is bounded" 15000 <|
    Async.block do
  for _ in [0:3] do
    let (client, peer) ← Mock.new
    let connection ← mkConnection client
      ({ readTimeout := ⟨30000, by decide⟩, requestTimeout := ⟨600, by decide⟩,
         keepAliveTimeout := ⟨30000, by decide⟩ } : Client.Config)
    try
      let result ← sendInBackground connection (mkRequest "/handover")
      discard <| readHead peer
      peer.send (rawResp "200 OK" #[("Content-Length", toString slowToPull.size)] "")
      let ⟨response, completion⟩ ← expectResponse result
      peer.send slowToPull
      sleep 100

      -- Registering signals interest, which starts the pull; the timer then wins while it runs.
      let timer ← Selector.sleep 1
      discard <| Selectable.one #[
        .case response.body.recvSelector (fun _ => pure true),
        .case timer (fun _ => pure false)
      ]

      discard <| settleWithin completion 3000 "an abandoned hand-over"
    finally
      connection.close

end ClientConnectionLifecycleTests
