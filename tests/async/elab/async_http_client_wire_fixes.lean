module

import Std.Http.Test.Helpers

/-! Regression tests for the HTTP client connection's handling of the wire: bytes that answer no
request, blocked writes, read backpressure, large chunks, abandoned bodies, and lenient parsing of
response heads. -/

open Std.Async
open Std Http Internal
open Test.ClientHelpers

def requestLine (bytes : ByteArray) : String :=
  ((String.fromUTF8! bytes).splitOn "\r\n").headD ""

def getReq (path : String) (method : Method := .get) : Async (Request Body.Empty) :=
  Request.new |>.method method |>.uri! path |>.empty

def expectBody (name : String) (p : IO.Promise (Except String (Response Body.Stream))) :
    Async String := do
  match ← await p.result! with
  | .error e => throw (IO.userError s!"{name} failed: {e}")
  | .ok response => response.body.readAll (α := String)

/-- A client over two mock transports, handed out one per connection. -/
def twoConnections : Async (TestClient × Mock.Client × Mock.Client) := do
  let (m0, s0) ← Mock.new
  let (m1, s1) ← Mock.new
  let (client, _) ← mkFollowingClient #[s0, s1]
  return (client, m0, m1)

-- A response that arrives on an idle connection answers nothing; the next request must get the
-- response the server gives it, on another connection.
#eval show IO _ from runWithTimeout "an unsolicited response is not delivered to the next request" 3000 <|
  Async.block do
  let (client, m0, m1) ← twoConnections
  let p1 ← sendInBackground client (← getReq "/one")
  discard <| drainRequest m0
  m0.send (rawResp "200 OK" #[("Content-Length", "3")] "one")
  unless (← expectBody "/one" p1) == "one" do throw (IO.userError "wrong body for /one")
  m0.send (rawResp "408 Request Timeout" #[("Content-Length", "0"), ("Connection", "close")] "")
  IO.sleep 100
  let p2 ← sendInBackground client (← getReq "/two")
  let line := requestLine (← drainRequest m1)
  unless line.startsWith "GET /two" do throw (IO.userError s!"unexpected request {line.quote}")
  m1.send (rawResp "200 OK" #[("Content-Length", "3")] "two")
  unless (← expectBody "/two" p2) == "two" do throw (IO.userError "/two got the unsolicited response")

-- Bytes past `Content-Length` arrive with the response; they must not become the next response.
#eval show IO _ from runWithTimeout "bytes past a response's end are not the next response" 3000 <|
  Async.block do
  let (client, m0, m1) ← twoConnections
  let p1 ← sendInBackground client (← getReq "/one")
  discard <| drainRequest m0
  let smuggled := rawResp "200 OK" #[("Content-Length", "8")] "smuggled"
  m0.send (rawResp "200 OK" #[("Content-Length", "2")] "ok" ++ smuggled)
  unless (← expectBody "/one" p1) == "ok" do throw (IO.userError "wrong body for /one")
  let p2 ← sendInBackground client (← getReq "/two")
  discard <| drainRequest m1
  m1.send (rawResp "200 OK" #[("Content-Length", "3")] "two")
  unless (← expectBody "/two" p2) == "two" do throw (IO.userError "/two got the smuggled response")

-- A HEAD response has no body, so bytes after its head belong to no response.
#eval show IO _ from runWithTimeout "stray bytes after a HEAD response do not break the next request" 3000 <|
  Async.block do
  let (client, m0, m1) ← twoConnections
  let p1 ← sendInBackground client (← getReq "/h" .head)
  discard <| drainRequest m0
  m0.send (rawResp "200 OK" #[("Content-Length", "5")] "" ++ "hello".toUTF8)
  discard <| expectBody "HEAD" p1
  let p2 ← sendInBackground client (← getReq "/two")
  discard <| drainRequest m1
  m1.send (rawResp "200 OK" #[("Content-Length", "3")] "two")
  unless (← expectBody "/two" p2) == "two" do throw (IO.userError "wrong body for /two")

/-- A mock transport whose writes block for a minute once `stall` is set: a peer that stopped
reading. -/
structure StallingTransport where
  inner : Mock.Server
  stall : IO.Ref Bool

instance : Transport StallingTransport where
  recv t n := Transport.recv t.inner n
  sendAll t data := do
    if ← t.stall.get then Std.Async.sleep 60000
    Transport.sendAll t.inner data
  recvSelector t n := Transport.recvSelector t.inner n
  close t := Transport.close t.inner

-- A write the peer never takes is bounded by `requestTimeout` like the rest of the exchange.
#eval show IO _ from runWithTimeout "a blocked write ends at requestTimeout" 3000 <|
  Async.block do
  let (_peer, server) ← Mock.new
  let stall ← IO.mkRef true
  let connection ← Client.Connection.new ({ inner := server, stall } : StallingTransport) (origin)
    { requestTimeout := ⟨300, by decide⟩ }
  let request ← Request.new |>.method .put |>.uri! "/upload" |>.text "payload"
  match ← connection.sendTracked { request with } with
  | .error .timeout => pure ()
  | .error e => throw (IO.userError s!"expected a timeout, got {e}")
  | .ok _ => throw (IO.userError "a stalled upload succeeded")

-- `close` reaches a connection blocked in a write.
#eval show IO _ from runWithTimeout "close ends a blocked write" 3000 <|
  Async.block do
  let (_peer, server) ← Mock.new
  let stall ← IO.mkRef true
  let connection ← Client.Connection.new ({ inner := server, stall } : StallingTransport) (origin)
  let request ← Request.new |>.method .put |>.uri! "/upload" |>.text "payload"
  let result : IO.Promise (Except Client.Error Client.TrackedResponse) ← IO.Promise.new
  background do discard <| result.resolve (← connection.sendTracked { request with })
  IO.sleep 200
  connection.close
  match ← await result.result! with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "a stalled upload succeeded after close")
  await connection.shutdown.result!

-- A consumer slower than the network does not make the connection buffer the whole body: reading
-- pauses while the caller has bytes in hand, so a body far larger than `maxBufferedBodyBytes` still
-- arrives whole.
#eval show IO _ from runWithTimeout "a slow consumer gets a body larger than the buffer limit" 8000 <|
  Async.block do
  let (mock, server) ← Mock.new
  let tc ← mkClient server { maxBufferedBodyBytes := 256 * 1024 }
  let p ← sendInBackground tc (← getReq "/big")
  discard <| drainRequest mock
  -- Past the 256 KiB limit plus the header allowance that comes on top of it.
  let total := 8 * 1024 * 1024
  let piece := ByteArray.mk (Array.replicate (64 * 1024) 120)
  mock.send (rawResp "200 OK" #[("Content-Length", toString total)] "")
  for _ in [0:total / piece.size] do
    mock.send piece
  let response ← match ← await p.result! with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"the request failed: {e}")
  IO.sleep 300
  let body ← response.body.readAll (α := ByteArray)
  unless body.size == total do
    throw (IO.userError s!"expected {total} bytes, got {body.size}")

-- One large chunk streams to the caller as it arrives, instead of reaching it only once the whole
-- chunk is in.
#eval show IO _ from runWithTimeout "a large chunk streams as it arrives" 4000 <|
  Async.block do
  let (mock, server) ← Mock.new
  let tc ← mkClient server
  let p ← sendInBackground tc (← getReq "/chunk")
  discard <| drainRequest mock
  let piece := ByteArray.mk (Array.replicate (64 * 1024) 120)
  -- A 1 MiB chunk, of which only the first 64 KiB is sent for now.
  mock.send (rawResp "200 OK" #[("Transfer-Encoding", "chunked")] "100000\r\n" ++ piece)
  let response ← match ← await p.result! with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"the request failed: {e}")
  let first ← Selectable.one #[
    .case (← Selector.sleep 1000) (fun _ => pure none),
    .case (response.body.recvSelector) (fun chunk => pure (some chunk))]
  match first with
  | some (some chunk) =>
    unless chunk.data.size > 0 do throw (IO.userError "the first piece was empty")
  | some none => throw (IO.userError "the body ended early")
  | none => throw (IO.userError "nothing of the chunk reached the caller before it was complete")
  response.body.close

-- Closing a body that is still arriving gives its connection up instead of holding it to read and
-- discard the rest; the next request goes out on a new connection at once.
#eval show IO _ from runWithTimeout "closing an unfinished body releases its connection" 3000 <|
  Async.block do
  let (m0, s0) ← Mock.new
  let (m1, s1) ← Mock.new
  let (tc, _) ← mkFollowingClient #[s0, s1] { maxConnectionsPerOrigin := ⟨1, by decide⟩ }
  let p1 ← sendInBackground tc (← getReq "/stream")
  discard <| drainRequest m0
  m0.send (rawResp "200 OK" #[("Transfer-Encoding", "chunked")] "6\r\nevent1\r\n")
  let response ← match ← await p1.result! with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"the first request failed: {e}")
  discard <| response.body.recv
  response.body.close
  background do
    for _ in [0:20] do
      IO.sleep 50
      try m0.send "6\r\neventN\r\n".toUTF8 catch _ => pure ()
  let p2 ← sendInBackground tc (← getReq "/next")
  discard <| drainRequest m1
  m1.send (rawResp "200 OK" #[("Content-Length", "2")] "ok")
  unless (← expectBody "/next" p2) == "ok" do throw (IO.userError "wrong body for /next")

-- obs-text in a header value or a reason phrase is opaque data, not a malformed response: raw UTF-8
-- is kept, and bytes that are not UTF-8 are replaced.
#eval show IO _ from runWithTimeout "obs-text in a header value or reason phrase is accepted" 3000 <|
  Async.block do
  let (mock, server) ← Mock.new
  let tc ← mkClient server
  let p ← sendInBackground tc (← getReq "/file")
  discard <| drainRequest mock
  let head := "HTTP/1.1 200 Trouvé\r\nContent-Disposition: attachment; filename=\"café.txt\"\r\nX-Latin1: ".toUTF8
    ++ ByteArray.mk #[0x63, 0x61, 0x66, 0xE9] ++ "\r\nContent-Length: 2\r\n\r\nok".toUTF8
  mock.send head
  match ← await p.result! with
  | .error e => throw (IO.userError s!"the response was rejected: {e}")
  | .ok response =>
    let some disposition := response.line.headers.get? (.mk "content-disposition")
      | throw (IO.userError "Content-Disposition is missing")
    unless disposition.value.contains "café.txt" do
      throw (IO.userError s!"the UTF-8 file name was not kept: {disposition.value.quote}")
    unless (← response.body.readAll (α := String)) == "ok" do throw (IO.userError "wrong body")

-- A status line that ends right after the code, with no space and no reason phrase, is accepted.
#eval show IO _ from runWithTimeout "a status line without a reason phrase or its space is accepted" 3000 <|
  Async.block do
  let (mock, server) ← Mock.new
  let tc ← mkClient server
  let p ← sendInBackground tc (← getReq "/bare")
  discard <| drainRequest mock
  mock.send "HTTP/1.1 200\r\nContent-Length: 2\r\n\r\nok".toUTF8
  match ← await p.result! with
  | .error e => throw (IO.userError s!"the response was rejected: {e}")
  | .ok response =>
    unless response.line.status == .ok do throw (IO.userError "wrong status")
    unless (← response.body.readAll (α := String)) == "ok" do throw (IO.userError "wrong body")
