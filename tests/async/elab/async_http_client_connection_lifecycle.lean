module

import Std.Http.Test.Helpers

/-!
Regression tests for the HTTP client's connection lifecycle, found while reviewing #14547: response
backpressure, request-body producer errors, and the bounds that apply to each wait an exchange parks
on.
-/

open Std.Async
open Std Http Internal
open Std.Http.Client
open Std.Http.Internal.Test.ClientHelpers

namespace ClientConnectionLifecycleTests

/--
A client whose connector hands out `transport` for its first connection and refuses any later one,
so every request runs over that one connection.
-/
private def mkConnection (transport : Mock.Client) (config : Client.Config) : Async TestClient := do
  let used ← IO.mkRef false
  let connect : Client.Connector := fun _ _ => do
    if ← used.modifyGet (fun u => (u, true)) then
      return .error (.connect "this test allows a single connection")
    return .ok (.of transport)
  let client ← Client.new config connect (maxRetries := 0)
  pure { client, origin := origin "example.com", opened := ← IO.mkRef #[] }

private def mkRequest (path : String)
    (body : Body.Any := Body.Any.ofBody ({} : Body.Empty)) : Request Body.Any :=
  { (Request.new |>.method .post |>.uri! path |>.header! "Host" "example.com").body body with }

private def sendInBackground (client : TestClient) (request : Request Body.Any) :
    Async (IO.Promise (Except Error (Response Body.Stream))) := do
  let promise ← IO.Promise.new
  background do
    promise.resolve (← client.client.trySend client.origin request)
  pure promise

private def expectResponse
    (promise : IO.Promise (Except Error (Response Body.Stream))) :
    Async (Response Body.Stream) := do
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
  | .notSent _ => ".notSent"
  | .protocol _ => ".protocol"
  | .bodyLimitExceeded => ".bodyLimitExceeded"
  | .invalidRequest _ => ".invalidRequest"
  | .io _ => ".io"
  | .cancelled => ".cancelled"

/--
Waits up to `ms` for the exchange behind `response` to end, which closes its body, then reports how
it ended: `.ok` for a clean end, or the message of the error the body was closed with.
-/
private def settleWithin (response : Response Body.Stream) (ms : Nat) (what : String) :
    Async (Except String Unit) := do
  for _ in [0:ms / 20] do
    if ← response.body.isClosed then
      return ← try
          let _ ← response.body.readAll (α := ByteArray)
          pure (.ok ())
        catch e => pure (.error (toString e))
    sleep 20
  throw (IO.userError s!"{what}: the exchange had not settled {ms}ms later")

/-- Asserts that the exchange ended on its deadline rather than on some other failure. -/
private def expectTimedOut (response : Response Body.Stream) (ms : Nat) (what : String) :
    Async Unit := do
  match ← settleWithin response ms what with
  | .error e =>
    unless e == toString Error.timeout do
      throw (IO.userError s!"{what}: expected .timeout, got {e.quote}")
  | .ok () => throw (IO.userError s!"{what}: the exchange reported success")

/-- Asserts that the client closes the connection within `ms`, discarding anything else it writes. -/
private def expectClosedWithin (peer : Mock.Server) (ms : Nat) (what : String) : Async Unit := do
  let closed ← IO.Promise.new
  background do
    try
      while (← peer.recv?).isSome do pure ()
    catch _ => pure ()
    closed.resolve ()
  for _ in [0:ms / 10] do
    if ← closed.isResolved then return
    sleep 10
  throw (IO.userError s!"{what}: the connection was still open {ms}ms later")

/--
Whether the connection was given up within `ms`: either it carries a second request, or it closed
(and the second request, needing a new connection, is refused by the connector).
-/
private def releasedWithin (client : TestClient) (peer : Mock.Server) (ms : Nat) : Async Bool := do
  discard <| sendInBackground client (mkRequest "/next")
  let released ← IO.Promise.new
  background do
    try discard <| readHead peer catch _ => pure ()
    released.resolve ()
  for _ in [0:ms / 10] do
    if ← released.isResolved then return true
    sleep 10
  return false

/-!
The read timeout bounds waits for network data, not time spent waiting for the caller to consume
body bytes that have already arrived.
-/
#eval show IO _ from runWithTimeout "buffered response body survives readTimeout" 3000 <|
    Async.block do
  let (transport, peer) ← Mock.new
  let client ← mkConnection transport
    ({ readTimeout := ⟨100, by decide⟩, requestTimeout := ⟨2000, by decide⟩,
       keepAliveTimeout := ⟨2000, by decide⟩ } : Client.Config)
  try
    let result ← sendInBackground client (mkRequest "/buffered")
    discard <| readHead peer
    peer.send (rawResp "200 OK" #[("Content-Length", "2")] "ok")
    let response ← expectResponse result

    sleep 250

    let body : String ← response.body.readAll
    unless body == "ok" do
      throw (IO.userError s!"expected buffered body \"ok\", got {body.quote}")
  finally
    client.client.close

/-!
An error raised by a request-body producer is an `.io` failure. It must not be collapsed into the
retryable `.closed` constructor merely because it arrives through a selector.
-/
#eval show IO _ from runWithTimeout "request body selector preserves producer error" 3000 <|
    Async.block do
  let (transport, peer) ← Mock.new
  let client ← mkConnection transport
    ({ readTimeout := ⟨2000, by decide⟩, requestTimeout := ⟨2000, by decide⟩ } : Client.Config)
  try
    let stream ← Body.mkStream
    stream.setKnownSize (some (.fixed 1))
    let result ← sendInBackground client
      (mkRequest "/body-error" (Body.Any.ofBody stream))
    discard <| readHead peer

    -- Let the client start pulling the request body before failing the producer.
    sleep 50
    stream.closeWithError (IO.userError "producer failed")

    match ← await result.result! with
    | .error (.io _) => pure ()
    | .error e =>
      throw (IO.userError s!"expected .io, got {errorConstructor e}")
    | .ok _ =>
      throw (IO.userError "expected the request-body failure to reject the request")
  finally
    client.client.close

/-!
The other side of that bound: with the peer silent and the body unread, the exchange is bounded by
`requestTimeout`, and that bound has to arrive.
-/
#eval show IO _ from runWithTimeout "an unread response body is bounded by requestTimeout" 6000 <|
    Async.block do
  let (transport, peer) ← Mock.new
  let client ← mkConnection transport
    ({ readTimeout := ⟨200, by decide⟩, requestTimeout := ⟨2000, by decide⟩,
       keepAliveTimeout := ⟨30000, by decide⟩ } : Client.Config)
  try
    let result ← sendInBackground client (mkRequest "/unread")
    discard <| readHead peer
    peer.send (rawResp "200 OK" #[("Content-Length", "10")] "abcd")
    let response ← expectResponse result

    -- Well clear of `readTimeout` and well short of `requestTimeout`, so neither a slow machine
    -- nor a fast one can decide this.
    sleep 600
    if ← response.body.isClosed then
      throw (IO.userError "the exchange ended while the caller still held an unread body: the \
        socket bound fired on a wait that was not the peer's")

    expectTimedOut response 3000 "an unread response body"
  finally
    client.client.close

/-!
A caller that closes a body that is still arriving is done with it: the client does not wait on the
peer to send the rest only to discard it, but ends the exchange, and so the connection, at once.
-/
#eval show IO _ from runWithTimeout "an abandoned unfinished response body ends the exchange" 6000 <|
    Async.block do
  let (transport, peer) ← Mock.new
  let client ← mkConnection transport
    ({ readTimeout := ⟨200, by decide⟩, requestTimeout := ⟨30000, by decide⟩,
       keepAliveTimeout := ⟨30000, by decide⟩ } : Client.Config)
  try
    let result ← sendInBackground client (mkRequest "/abandoned")
    discard <| readHead peer
    peer.send (rawResp "200 OK" #[("Content-Length", "10")] "abcd")
    let response ← expectResponse result

    response.body.close

    expectClosedWithin peer 150 "an abandoned response body"
  finally
    client.client.close

/-!
A caller that consumed everything buffered is waiting on the peer again, even though the reader is
still on the body: the pull that empties the buffer re-arms the bound.
-/
#eval show IO _ from runWithTimeout "a drained response body re-arms readTimeout" 6000 <|
    Async.block do
  let (transport, peer) ← Mock.new
  let client ← mkConnection transport
    ({ readTimeout := ⟨300, by decide⟩, requestTimeout := ⟨30000, by decide⟩,
       keepAliveTimeout := ⟨30000, by decide⟩ } : Client.Config)
  try
    let result ← sendInBackground client (mkRequest "/drained")
    discard <| readHead peer
    peer.send (rawResp "200 OK" #[("Transfer-Encoding", "chunked")] "")
    peer.send (Test.chunk "abc").toUTF8
    let response ← expectResponse result

    let some chunk ← response.body.recv
      | throw (IO.userError "expected the chunk the peer sent")
    unless String.fromUTF8! chunk.data == "abc" do
      throw (IO.userError s!"expected chunk \"abc\", got {(String.fromUTF8! chunk.data).quote}")

    expectTimedOut response 3000 "a drained response body"
  finally
    client.client.close

/-!
The same bound seen from the request side: a peer that is receiving a request is silent by
definition, so a caller producing its body in slow bursts must not have its own upload timed out.
-/
#eval show IO _ from runWithTimeout "a slow request body does not trip readTimeout" 8000 <|
    Async.block do
  let (transport, peer) ← Mock.new
  let client ← mkConnection transport
    ({ readTimeout := ⟨200, by decide⟩, requestTimeout := ⟨6000, by decide⟩,
       keepAliveTimeout := ⟨6000, by decide⟩ } : Client.Config)
  try
    let stream ← Body.mkStream
    stream.setKnownSize (some (.fixed 6))
    let result ← sendInBackground client
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

    let response ← expectResponse result
    unless response.line.status.toCode == 200 do
      throw (IO.userError s!"expected 200, got {response.line.status.toCode}")
  finally
    client.client.close

/-!
That stand-down is scoped to the upload: with the request body on the wire the client is waiting on
the peer again, and `readTimeout` — not the far longer `requestTimeout` — is what ends the wait.
-/
#eval show IO _ from runWithTimeout "readTimeout re-arms once the request body is sent" 5000 <|
    Async.block do
  let (transport, peer) ← Mock.new
  let client ← mkConnection transport
    ({ readTimeout := ⟨200, by decide⟩, requestTimeout := ⟨30000, by decide⟩,
       keepAliveTimeout := ⟨30000, by decide⟩ } : Client.Config)
  try
    let stream ← Body.mkStream
    stream.setKnownSize (some (.fixed 3))
    let result ← sendInBackground client
      (mkRequest "/finished-upload" (Body.Any.ofBody stream))
    discard <| readHead peer
    stream.send (Chunk.ofByteArray "abc".toUTF8)
    stream.close

    match ← await result.result! with
    | .error .timeout => pure ()
    | .error e => throw (IO.userError s!"expected .timeout, got {errorConstructor e}")
    | .ok _ => throw (IO.userError "the exchange reported success")
  finally
    client.client.close

/--
A body large enough that pulling it takes longer than the timer the read below is raced against, so
the consumer is reliably gone by the time the client hands the chunk over.
-/
private def slowToPull : ByteArray := Id.run do
  let mut bytes := ("x".pushn 'y' 1023).toUTF8
  for _ in [0:14] do
    bytes := bytes ++ bytes
  return bytes

/-!
A registered consumer reports only that someone was waiting when the client looked. A consumer racing
that read against something else can lose and be gone before the client hands the chunk over.
However the race falls, the exchange has to end and give up its connection.

A machine fast enough for the read to win the race leaves nothing here to catch, which makes this
test weaker rather than flaky.
-/
#eval show IO _ from runWithTimeout "a hand-over the consumer walked away from is bounded" 15000 <|
    Async.block do
  for _ in [0:3] do
    let (transport, peer) ← Mock.new
    let client ← mkConnection transport
      ({ readTimeout := ⟨30000, by decide⟩, requestTimeout := ⟨600, by decide⟩,
         keepAliveTimeout := ⟨30000, by decide⟩ } : Client.Config)
    try
      let result ← sendInBackground client (mkRequest "/handover")
      discard <| readHead peer
      peer.send (rawResp "200 OK" #[("Content-Length", toString slowToPull.size)] "")
      let response ← expectResponse result
      peer.send slowToPull
      sleep 100

      -- Registering signals interest, which starts the pull; the timer then wins while it runs.
      let timer ← Selector.sleep 1
      discard <| Selectable.one #[
        .case response.body.recvSelector (fun _ => pure true),
        .case timer (fun _ => pure false)
      ]

      unless ← releasedWithin client peer 3000 do
        throw (IO.userError "an abandoned hand-over: the exchange still held its connection \
          3000ms later")
    finally
      client.client.close

end ClientConnectionLifecycleTests
