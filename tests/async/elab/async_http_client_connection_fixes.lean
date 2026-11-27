module

import Std.Http.Test.Helpers

/-!
Regression tests for the HTTP client's handling of a single connection:
* an upload whose bytes are still moving trips neither `readTimeout` nor `requestTimeout`;
* an early response is delivered while the upload's write is blocked;
* a failed upload write keeps a response that has already arrived;
* a request whose head was never written fails as `.notSent`, and bytes the peer sends before it
  are not its response;
* `Expect: 100-continue` keeps a declared `Content-Length`;
* a cookie handler whose `store` raises fails neither the response nor its connection;
* closing a response body after a read that timed out releases the connection.
-/

open Std.Async
open Std Http Internal
open Test.ClientHelpers

def getReq (path : String) : Async (Request Body.Empty) :=
  Request.new |>.method .get |>.uri! path |>.empty

/--
A client whose connector hands out `transport` for its first connection and refuses any later one,
so every request runs over that one connection.
-/
def mkConnection {α : Type} [Transport α] (transport : α) (config : Client.Config := {}) :
    Async TestClient := do
  let used ← IO.mkRef false
  let connect : Client.Connector := fun _ _ => do
    if ← used.modifyGet (fun u => (u, true)) then
      return .error (.connect "this test allows a single connection")
    return .ok (.of transport)
  let client ← Client.new config connect (maxRetries := 0)
  pure { client, origin := origin, opened := ← IO.mkRef #[] }

def trySend {β : Type} [Coe β Body.Any] (self : TestClient) (request : Request β) :
    Async (Except Client.Error (Response Body.Stream)) :=
  self.client.trySend self.origin request

/-- Resolves once the client closes the connection, reading off everything it still writes. -/
def whenClosed (peer : Mock.Client) : Async (IO.Promise Unit) := do
  let closed ← IO.Promise.new
  background do
    try
      while (← peer.recv?).isSome do pure ()
    catch _ => pure ()
    closed.resolve ()
  pure closed

namespace UploadTimeouts

/-- A transport whose writes complete at about 1 KiB per millisecond, like a large upload over a
real link: `sendAll` returns once the bytes have left, not before. -/
structure SlowLink where
  inner : Mock.Server

instance : Transport SlowLink where
  recv t n := Transport.recv t.inner n
  sendAll t data := do
    let size := data.foldl (fun acc b => acc + b.size) 0
    let ms := size / 1024
    if ms > 0 then Std.Async.sleep (Std.Time.Millisecond.Offset.ofNat ms)
    Transport.sendAll t.inner data
  recvSelector t n := Transport.recvSelector t.inner n
  close t := Transport.close t.inner

def upload (size : Nat) : Async (Request Body.Full) :=
  Request.new |>.method .put |>.uri! "/upload"
    |>.bytes (ByteArray.mk (Array.replicate size 120))

def answerOnceReceived (peer : Mock.Client) : Async Unit := do
  try
    discard <| drainRequest peer
    peer.send (rawResp "200 OK" #[("Content-Length", "2")] "ok")
  catch _ => pure ()

def expectUploaded (config : Client.Config) (size : Nat) : Async Unit := do
  let (peer, server) ← Mock.new
  let client ← mkConnection ({ inner := server } : SlowLink) config
  background (answerOnceReceived peer)
  let start ← IO.monoMsNow
  let result ← trySend client (← upload size)
  let elapsed := (← IO.monoMsNow) - start
  client.client.close
  match result with
  | .ok response =>
    unless response.line.status.toCode == 200 do
      throw (IO.userError s!"expected 200, got {response.line.status.toCode}")
  | .error e =>
    throw (IO.userError s!"the upload failed after {elapsed} ms while its write was still in progress: {e}")

-- `readTimeout` bounds silence from the peer while the client waits on it, not a write in progress.
#eval show IO _ from runWithTimeout "an upload slower than readTimeout succeeds" 8000 <| Async.block do
  expectUploaded { readTimeout := ⟨300, by decide⟩, requestTimeout := ⟨10000, by decide⟩ }
    (1024 * 1024)

-- `requestTimeout` bounds each pause, so a body that is one write moves the deadline as it goes out.
#eval show IO _ from runWithTimeout "an upload whose one write outlasts requestTimeout succeeds" 8000 <|
  Async.block do
  expectUploaded { readTimeout := ⟨30000, by decide⟩, requestTimeout := ⟨500, by decide⟩ }
    (2 * 1024 * 1024)

end UploadTimeouts

namespace EarlyResponse

/-- A transport whose writes after the first block until `release` resolves: a peer that has read
the request head and stopped reading. -/
structure StallAfterHead where
  inner : Mock.Server
  writes : IO.Ref Nat
  release : IO.Promise Unit

instance : Transport StallAfterHead where
  recv t n := Transport.recv t.inner n
  sendAll t data := do
    let index ← t.writes.modifyGet fun i => (i, i + 1)
    if index ≥ 1 then discard <| await t.release.result?
    Transport.sendAll t.inner data
  recvSelector t n := Transport.recvSelector t.inner n
  close t := Transport.close t.inner

/-- Sends a PUT whose body write blocks, answers it with a `401` carrying `headers` and `body`, and
returns the response once its head is delivered, with the client and the write's release. -/
def answerEarly (headers : Array (String × String)) (body : String) :
    Async (Except Client.Error (Response Body.Stream) × Nat × TestClient × IO.Promise Unit) := do
  let (peer, server) ← Mock.new
  let writes ← IO.mkRef 0
  let release ← IO.Promise.new
  let client ← mkConnection ({ inner := server, writes, release } : StallAfterHead)
    { requestTimeout := ⟨1500, by decide⟩ }
  let request ← Request.new |>.method .put |>.uri! "/upload" |>.text "payload"
  let result : IO.Promise (Except Client.Error (Response Body.Stream)) ← IO.Promise.new
  background do discard <| result.resolve (← trySend client request)
  discard <| peer.recv?
  IO.sleep 100
  let start ← IO.monoMsNow
  peer.send (rawResp "401 Unauthorized" headers body)
  let outcome ← await result.result!
  return (outcome, (← IO.monoMsNow) - start, client, release)

def expect401 (headers : Array (String × String)) : Async Unit := do
  let (outcome, ms, client, release) ← answerEarly headers ""
  release.resolve ()
  client.client.close
  match outcome with
  | .ok response =>
    if response.line.status.toCode != 401 then
      throw (IO.userError s!"expected the 401, got {response.line.status.toCode}")
    else if ms > 1000 then
      throw (IO.userError s!"the 401 took {ms} ms to reach the caller")
  | .error e =>
    throw (IO.userError s!"the early 401 was lost; the caller got `{e}` after {ms} ms")

#eval show IO _ from runWithTimeout "early 401 with Connection: close during a blocked write" 5000 <|
  Async.block do
  expect401 #[("Content-Length", "0"), ("Connection", "close")]

-- A keep-alive response that ends at its head completes the exchange in the same step; it reaches
-- the caller before the exchange waits for the blocked write.
#eval show IO _ from runWithTimeout "early keep-alive 401 during a blocked write" 5000 <|
  Async.block do
  expect401 #[("Content-Length", "0")]

-- The body of an early keep-alive response, already received, is readable to its end while the
-- write is still blocked.
#eval show IO _ from runWithTimeout "an early keep-alive body is readable while the write is blocked" 5000 <|
  Async.block do
  let (outcome, _, client, release) ← answerEarly #[("Content-Length", "6")] "denied"
  let response ← match outcome with
    | .ok response => pure response
    | .error e => throw (IO.userError s!"the 401 head was lost: {e}")
  let start ← IO.monoMsNow
  let body ← response.body.readAll (α := String)
  let elapsed := (← IO.monoMsNow) - start
  release.resolve ()
  client.client.close
  unless body == "denied" do throw (IO.userError s!"wrong body {body.quote}")
  if elapsed > 1000 then
    throw (IO.userError s!"the 6-byte body, already received, took {elapsed} ms to read")

end EarlyResponse

namespace FailedUploadWrite

/-- A transport whose writes after the first wait for `fail` and then raise: a peer that read the
request head, answered, and closed while the body was still being written. -/
structure FailAfterHead where
  inner : Mock.Server
  writes : IO.Ref Nat
  fail : IO.Promise Unit

instance : Transport FailAfterHead where
  recv t n := Transport.recv t.inner n
  sendAll t data := do
    let index ← t.writes.modifyGet fun i => (i, i + 1)
    if index ≥ 1 then
      discard <| await t.fail.result?
      throw (IO.userError "Broken pipe")
    Transport.sendAll t.inner data
  recvSelector t n := Transport.recvSelector t.inner n
  close t := Transport.close t.inner

def scenario (failWrite : Bool) : Async Unit := do
  let (peer, server) ← Mock.new
  let writes ← IO.mkRef 0
  let fail ← IO.Promise.new
  let client ← mkConnection ({ inner := server, writes, fail } : FailAfterHead)
    { requestTimeout := ⟨3000, by decide⟩ }
  let request ← Request.new |>.method .put |>.uri! "/upload" |>.text "a large upload"
  let result : IO.Promise (Except Client.Error (Response Body.Stream)) ← IO.Promise.new
  background do discard <| result.resolve (← trySend client request)
  discard <| peer.recv?
  peer.send (rawResp "413 Content Too Large"
    #[("Content-Length", "13"), ("Connection", "close")] "too large: no")
  let response ← match ← await result.result! with
    | .ok response => pure response
    | .error e => throw (IO.userError s!"the 413 head was not delivered: {e}")
  unless response.line.status.toCode == 413 do
    throw (IO.userError s!"expected 413, got {response.line.status.toCode}")
  -- The whole response is in the client's hands; now the peer's close breaks the write.
  IO.sleep 100
  if failWrite then
    fail.resolve ()
    IO.sleep 100
  let body ← try response.body.readAll (α := String)
    catch e => throw (IO.userError s!"reading the received 413 body failed: {e}")
  unless body == "too large: no" do
    throw (IO.userError s!"expected the 413 body, got {body.quote}")
  fail.resolve ()
  client.client.close

#eval show IO _ from runWithTimeout "the 413 body arrives while the write is pending" 5000 <|
  Async.block (scenario false)

#eval show IO _ from runWithTimeout "a failed write keeps the received 413 body" 5000 <|
  Async.block (scenario true)

end FailedUploadWrite

namespace DeferredHead

/-- A POST whose streamed body has produced nothing yet, so the writer still holds back its head. -/
def pendingUpload : Async (Request Body.Any × Body.Stream) := do
  let body ← Body.mkStream
  let request := Request.new |>.method .post |>.uri! "/submit" |>.body body
  return ({ request with }, body)

-- Once the head has gone out, a close is reported as `.closed`.
#eval show IO _ from runWithTimeout "a close after the head is .closed" 3000 <|
  Async.block do
  let (peer, server) ← Mock.new
  let client ← mkConnection server
  let (request, body) ← pendingUpload
  let result : IO.Promise (Except Client.Error (Response Body.Stream)) ← IO.Promise.new
  background do discard <| result.resolve (← trySend client request)
  background do try body.send (Chunk.ofByteArray "x".toUTF8) catch _ => pure ()
  let some _ ← peer.recv? | throw (IO.userError "the head never arrived")
  peer.close
  match ← await result.result! with
  | .error (.closed _) => pure ()
  | .error e => throw (IO.userError s!"unexpected error {e}")
  | .ok _ => throw (IO.userError "the exchange succeeded")

-- Nothing of the request was written, so it can be resent whatever its method.
#eval show IO _ from runWithTimeout "a close before the deferred head is notSent" 3000 <|
  Async.block do
  let (peer, server) ← Mock.new
  let client ← mkConnection server
  let (request, body) ← pendingUpload
  let result : IO.Promise (Except Client.Error (Response Body.Stream)) ← IO.Promise.new
  background do discard <| result.resolve (← trySend client request)
  IO.sleep 200
  if let some bytes ← peer.tryRecv? then
    throw (IO.userError s!"setup: the head was written: {(String.fromUTF8! bytes).quote}")
  peer.close
  let outcome ← await result.result!
  body.close
  match outcome with
  | .error (.notSent _) => pure ()
  | .error e =>
    throw (IO.userError s!"nothing was written, yet the request failed as `{e}` (retryable: \
      {e.isRetryable}, never sent: {e.isNeverSent}) instead of .notSent")
  | .ok _ => throw (IO.userError "the exchange succeeded")

-- An unsolicited `408`, as a server sends before closing an idle connection, does not answer a
-- request whose head never left.
#eval show IO _ from runWithTimeout "an unsolicited 408 before the deferred head is not the response" 3000 <|
  Async.block do
  let (peer, server) ← Mock.new
  let client ← mkConnection server
  let (request, body) ← pendingUpload
  let result : IO.Promise (Except Client.Error (Response Body.Stream)) ← IO.Promise.new
  background do discard <| result.resolve (← trySend client request)
  IO.sleep 200
  if let some bytes ← peer.tryRecv? then
    throw (IO.userError s!"setup: the head was written: {(String.fromUTF8! bytes).quote}")
  peer.send (rawResp "408 Request Timeout" #[("Content-Length", "0"), ("Connection", "close")] "")
  let outcome ← await result.result!
  body.close
  match outcome with
  | .ok response =>
    throw (IO.userError s!"the request was never written, yet the caller got the peer's \
      {response.line.status.toCode} as its response")
  | .error _ => pure ()

end DeferredHead

namespace ExpectContinueLength

/-- Sends a streamed PUT with `Content-Length: 5` and returns its head as it reached the peer. -/
def headOf (expect : Bool) : Async String := do
  let (peer, server) ← Mock.new
  let client ← mkConnection server
    { requestTimeout := ⟨1000, by decide⟩, expectContinueTimeout := ⟨100, by decide⟩ }
  let body ← Body.mkStream
  let builder := Request.new |>.method .put |>.uri! "/object"
    |>.header Header.Name.contentLength (Header.Value.ofString! "5")
  let builder := if expect then builder.header Header.Name.expect (Header.Value.ofString! "100-continue")
    else builder
  let request := builder.body body
  background do discard <| trySend client request
  background do
    try
      body.send (Chunk.ofByteArray "hello".toUTF8)
      body.close
    catch _ => pure ()
  let mut bytes := ByteArray.empty
  while !(String.fromUTF8! bytes).contains "\r\n\r\n" do
    let some more ← peer.recv? | throw (IO.userError "no request head arrived")
    bytes := bytes ++ more
  client.client.close
  let text := String.fromUTF8! bytes
  return ((text.splitOn "\r\n\r\n").headD "").toLower

#eval show IO _ from runWithTimeout "Content-Length is kept without Expect" 3000 <|
  Async.block do
  let head ← headOf false
  unless head.contains "content-length: 5" do
    throw (IO.userError s!"no Content-Length in {head.quote}")

#eval show IO _ from runWithTimeout "Content-Length is kept with Expect: 100-continue" 3000 <|
  Async.block do
  let head ← headOf true
  unless head.contains "content-length: 5" ∧ ¬head.contains "transfer-encoding" do
    throw (IO.userError s!"the declared Content-Length was replaced: {head.quote}")

end ExpectContinueLength

namespace FailingHook

def failingStore : Client.CookieHandler where
  load _ _ := pure #[]
  store _ _ _ := throw (IO.userError "cookie jar is read-only")

/-- Waits until the connection carries a second request or closes, for at most `ms` milliseconds,
and reports whether it did. A second request after a close needs a new connection, which the
connector refuses. -/
def releasedWithin (client : TestClient) (peer : Mock.Client) (ms : Nat) : Async Bool := do
  background do discard <| trySend client (← getReq "/two")
  let released : IO.Promise Unit ← IO.Promise.new
  background do
    try discard <| drainRequest peer catch _ => pure ()
    released.resolve ()
  for _ in [0:ms / 10] do
    if ← released.isResolved then return true
    IO.sleep 10
  return false

-- A caller that closes the body releases the connection at once.
#eval show IO _ from runWithTimeout "closing the body releases the connection" 8000 <|
  Async.block do
  let (peer, server) ← Mock.new
  let client ← mkConnection server
    { requestTimeout := ⟨4000, by decide⟩, keepAliveTimeout := ⟨30000, by decide⟩ }
  let first : IO.Promise (Except Client.Error (Response Body.Stream)) ← IO.Promise.new
  background do discard <| first.resolve (← trySend client (← getReq "/one"))
  discard <| drainRequest peer
  peer.send (rawResp "200 OK" #[("Content-Length", "5")] "hello")
  let response ← match ← await first.result! with
    | .ok response => pure response
    | .error e => throw (IO.userError s!"setup: {e}")
  response.body.close
  let released ← releasedWithin client peer 1000
  client.client.close
  unless released do throw (IO.userError "the closed body held its connection for over 1000 ms")

-- A cookie handler that cannot store the response's cookies does not fail the request: the caller
-- gets the response, and the connection carries the next request.
#eval show IO _ from runWithTimeout "a failing cookie store fails neither the response nor its connection" 8000 <|
  Async.block do
  let (peer, server) ← Mock.new
  let client ← mkConnection server
    { cookieHandler := some failingStore, requestTimeout := ⟨4000, by decide⟩,
      keepAliveTimeout := ⟨30000, by decide⟩ }
  let first : IO.Promise (Except Client.Error (Response Body.Stream)) ← IO.Promise.new
  background do discard <| first.resolve (← trySend client (← getReq "/one"))
  discard <| drainRequest peer
  peer.send (rawResp "200 OK" #[("Content-Length", "5")] "hello")
  match ← await first.result! with
  | .error e => throw (IO.userError s!"the failing store failed the request: {e}")
  | .ok response =>
    unless (← response.body.readAll (α := String)) == "hello" do throw (IO.userError "wrong body")
  let released ← releasedWithin client peer 1000
  client.client.close
  unless released do
    throw (IO.userError "the response held its connection for over 1000 ms")

end FailingHook

namespace StalledBodyClose

/-- Opens an event stream, takes its first event, and returns the response with the peer silent. -/
def openStream : Async (TestClient × Response Body.Stream × Mock.Client) := do
  let (peer, server) ← Mock.new
  let client ← mkConnection server
    { readTimeout := ⟨3000, by decide⟩, requestTimeout := ⟨20000, by decide⟩ }
  let result : IO.Promise (Except Client.Error (Response Body.Stream)) ← IO.Promise.new
  background do discard <| result.resolve (← trySend client (← getReq "/events"))
  discard <| drainRequest peer
  peer.send (rawResp "200 OK" #[("Transfer-Encoding", "chunked")] "6\r\nevent1\r\n")
  let response ← match ← await result.result! with
    | .ok response => pure response
    | .error e => throw (IO.userError s!"setup: {e}")
  let some _ ← response.body.recv | throw (IO.userError "setup: no first event")
  return (client, response, peer)

/-- The time until the client closes the connection, which a body abandoned mid-stream leaves
unusable. -/
def timeToRelease (peer : Mock.Client) : Async Nat := do
  let start ← IO.monoMsNow
  let closed ← whenClosed peer
  repeat
    if ← closed.isResolved then break
    IO.sleep 20
  return (← IO.monoMsNow) - start

#eval show IO _ from runWithTimeout "closing an idle body releases the connection" 8000 <|
  Async.block do
  let (client, response, peer) ← openStream
  IO.sleep 100
  response.body.close
  let ms ← timeToRelease peer
  client.client.close
  if ms > 1000 then throw (IO.userError s!"released after {ms} ms")

-- The caller waits 200 ms for the next event, gives up, and closes the body; the connection hears
-- the close although the stream is stalled on the peer.
#eval show IO _ from runWithTimeout "closing a body after a timed-out read releases the connection" 8000 <|
  Async.block do
  let (client, response, peer) ← openStream
  let next ← Selectable.one #[
    .case response.body.recvSelector (fun chunk => pure (some chunk)),
    .case (← Selector.sleep 200) (fun _ => pure none)]
  if next.isSome then throw (IO.userError "setup: an event arrived")
  response.body.close
  let ms ← timeToRelease peer
  client.client.close
  if ms > 1000 then
    throw (IO.userError s!"the closed body held its connection for {ms} ms \
      (readTimeout is 3000 ms)")

end StalledBodyClose
