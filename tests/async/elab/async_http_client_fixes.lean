module

import Std.Http.Test.Helpers

/-!
Regression tests for `Client`:
* a proxied absolute-form target carries no userinfo or fragment;
* every redirect hop of a retried request uses a fresh connection;
* a numeric host spelling is not a domain name that reaches `127.0.0.1`;
* over TCP, an upload slower than `readTimeout` succeeds while it keeps moving.
-/

open Std.Async
open Std Http Internal
open Test.ClientHelpers

def getReq (path : String) : Async (Request Body.Empty) :=
  Request.new |>.method .get |>.uri! path |>.empty

/-- A connector that serves the `n`th connection it opens with `serve n`. -/
def servingConnector (dials : IO.Ref Nat) (serve : Nat → Mock.Client → Async Unit) :
    Client.Connector := fun origin config => do
  let (mock, server) ← Mock.new
  let n ← dials.modifyGet fun n => (n, n + 1)
  background (serve n mock)
  return .ok (Client.AnyTransport.of server)

def serveAll (body : String) (mock : Mock.Client) : Async Unit := do
  repeat
    let request ← try some <$> drainRequest mock catch _ => pure none
    if request.isNone then break
    mock.send (rawResp "200 OK" #[("Content-Length", toString body.length)] body)

def loopback4 : Net.IPv4Addr := Net.IPv4Addr.ofParts 127 0 0 1

namespace DroppedResponse

/-- Answers the first request with `firstStatus` and a 4-byte body, every later one with `200 ok`. -/
def serveFirst (answered : IO.Ref Nat) (firstStatus : String) : Nat → Mock.Client → Async Unit :=
  fun _ mock => do
    repeat
      let request ← try some <$> drainRequest mock catch _ => pure none
      if request.isNone then break
      if (← answered.modifyGet fun n => (n, n + 1)) == 0 then
        mock.send (rawResp firstStatus #[("Content-Length", "4")] "busy")
      else
        mock.send (rawResp "200 OK" #[("Content-Length", "2")] "ok")

end DroppedResponse

namespace ProxiedTarget

def target : RequestTarget :=
  .absoluteForm (URI.parse! "http://alice:s3cret@example.com/p?q=1#frag")

def requestLine (bytes : ByteArray) : String :=
  ((String.fromUTF8! bytes).splitOn "\r\n").headD ""

/-- Sends `GET target` on a client built from `config` and returns the request line on the wire. -/
def wireLine (config : Client.Config) : Async String := do
  let (mock, server) ← Mock.new
  let client ← mkClient server config
  let pending ← sendInBackground client (← Request.new |>.method .get |>.uri target |>.empty)
  let line := requestLine (← drainRequest mock)
  mock.send (rawResp "200 OK" #[("Content-Length", "0")] "")
  match ← await pending.result! with
  | .ok _ => pure line
  | .error e => throw (IO.userError s!"the request failed: {e}")

#eval show IO _ from
  runWithTimeout "a direct connection drops userinfo and fragment" 3000 <|
  Async.block do
  let line ← wireLine {}
  unless line == "GET /p?q=1 HTTP/1.1" do
    throw (IO.userError s!"unexpected direct request line {line.quote}")

-- RFC 9110 §4.2.4 forbids userinfo in a target, and absolute-form (RFC 9112 §3.2.2) has no
-- fragment, so neither reaches the proxy's request line.
#eval show IO _ from
  runWithTimeout "a proxied absolute-form target carries no userinfo or fragment" 3000 <|
  Async.block do
  let line ← wireLine { proxySelector := .of "proxy.local" 3128 }
  if line.contains "s3cret" || line.contains "alice" || line.contains "#" then
    throw (IO.userError s!"the proxy was sent {line.quote}")
  unless line == "GET http://example.com/p?q=1 HTTP/1.1" do
    throw (IO.userError s!"unexpected proxied request line {line.quote}")

end ProxiedTarget

namespace CloseBeforeCheckout

def expectClosed (what : String) (dials : IO.Ref Nat)
    (result : Except Client.Error (Response Body.Stream)) : Async Unit := do
  match result with
  | .error (.closed _) => pure ()
  | .error e => throw (IO.userError s!"{what}: expected a `.closed` failure, got {e}")
  | .ok response =>
    throw (IO.userError
      s!"{what}: the request started before `Client.close` completed with \
        {response.line.status.toCode} on a connection opened after it (dials: {← dials.get})")

end CloseBeforeCheckout

namespace RetryRedirectHop

def target : URI.Origin := origin "other.com"

/--
`example.com` answers every request with a redirect to `other.com`. Each `other.com` connection
answers its first request after a short delay (so that two primers run on two connections), then
closes when the next request arrives, the way a restarted server drops its old keep-alive sockets.
-/
def serve (hopOrigin : URI.Origin) (mock : Mock.Client) : Async Unit := do
  if hopOrigin == target then
    discard <| drainRequest mock
    IO.sleep 100
    mock.send (rawResp "200 OK" #[("Content-Length", "1")] "b")
    discard <| try some <$> drainRequest mock catch _ => pure none
    mock.close
  else
    repeat
      let request ← try some <$> drainRequest mock catch _ => pure none
      if request.isNone then break
      mock.send (rawResp "302 Found" #[("Location", "http://other.com/b"), ("Content-Length", "0")] "")

-- The first attempt's redirect hop takes one stale idle connection to `other.com`; the retry's hop
-- must open a fresh one rather than take the other stale one.
#eval show IO _ from
  runWithTimeout "a retry after a failed redirect hop does not reuse that origin's idle connection" 5000 <|
  Async.block do
  let dials ← IO.mkRef (#[] : Array URI.Origin)
  let connector : Client.Connector := fun hopOrigin config => do
    let (mock, server) ← Mock.new
    dials.modify (·.push hopOrigin)
    background (serve hopOrigin mock)
    return .ok (Client.AnyTransport.of server)
  let client ← Client.new {} connector (maxRetries := 1)

  -- Two concurrent requests leave two idle connections to `other.com`.
  let p1 ← async (t := AsyncTask) (client.trySend target (← getReq "/prime1"))
  let p2 ← async (t := AsyncTask) (client.trySend target (← getReq "/prime2"))
  for p in #[p1, p2] do
    match ← await p with
    | .ok response => discard <| response.body.readAll (α := ByteArray)
    | .error e => throw (IO.userError s!"setup: priming failed: {e}")
  unless (← dials.get).size == 2 do
    throw (IO.userError s!"setup: expected two connections to other.com, got {(← dials.get).size}")

  match ← client.trySend (origin "example.com") (← getReq "/start") with
  | .ok response =>
    let body ← response.body.readAll (α := String)
    unless body == "b" do throw (IO.userError s!"unexpected body {body.quote}")
  | .error e =>
    let toOther := (← dials.get).filter (· == target) |>.size
    let toStart := (← dials.get).size - toOther
    throw (IO.userError
      s!"the retried GET failed with {e}: example.com was dialled {toStart} times but other.com \
        only {toOther} times, so the retry's second hop reused a stale idle connection")

end RetryRedirectHop

namespace NumericHosts

def okPeer (_ : Request Body.Stream) : ContextAsync (Response Body.Any) :=
  Response.ok |>.text "loopback"

-- The system resolver reads `127.1`, `2130706433` and `0x7f.0.0.1` as `127.0.0.1`. A URL with such a
-- host must not parse as a domain name and still reach the loopback server.
#eval show IO _ from runWithTimeout "a numeric host name is not a domain name that reaches 127.0.0.1" 8000 <|
  Async.block do
  let server ← Server.serve (.v4 ⟨loopback4, 0⟩) okPeer
  let some (.v4 bound) := server.localAddr | throw (IO.userError "no local address")
  let port := bound.port
  let client ← Client.new {} (maxRetries := 0)
  let some dotted := (URI.parse? s!"http://127.0.0.1:{port}/").bind (·.origin?)
    | throw (IO.userError "http://127.0.0.1/ did not parse")
  unless dotted.host matches .ipv4 _ do
    throw (IO.userError "127.0.0.1 is not an IPv4 host")
  let mut confused := #[]
  for spelling in #["127.1", "2130706433", "0x7f.0.0.1"] do
    let url := s!"http://{spelling}:{port}/"
    let some target := (URI.parse? url).bind (·.origin?) | continue
    let .name _ := target.host | continue
    match ← client.tryGet url with
    | .ok response =>
      let body ← response.body.readAll (α := String)
      if body == "loopback" then confused := confused.push spelling
    | .error _ => pure ()
  server.shutdownAndWait
  unless confused.isEmpty do
    throw (IO.userError
      s!"hosts parsed as domain names reached the 127.0.0.1 server: {confused}")

end NumericHosts

namespace TcpUploadTimeout

/-- Reads the first 8 MiB of the upload slowly, so the client's writes complete only as fast as the
server consumes them, and the rest at full speed: once the client's last write is done, whatever the
kernel's socket buffers still hold counts against `readTimeout` like any wait for a response. -/
def slowReader (received : IO.Ref Nat) (req : Request Body.Stream) :
    ContextAsync (Response Body.Any) := do
  repeat
    let some chunk ← (req.body.recv : Async (Option Chunk)) | break
    received.modify (· + chunk.data.size)
    if (← received.get) < 8 * 1024 * 1024 then
      (Std.Async.sleep 5 : Async Unit)
  Response.ok |>.text s!"{← received.get}"

#eval show IO _ from runWithTimeout "TCP: an upload slower than readTimeout succeeds" 30000 <|
  Async.block do
  let received ← IO.mkRef 0
  let server ← Server.serve (.v4 ⟨loopback4, 0⟩) (slowReader received)
  let port ← match server.localAddr with
    | some (.v4 a) => pure a.port
    | _ => throw (IO.userError "no local address")
  let target : URI.Origin := { scheme := URI.Scheme.ofString! "http", host := .ipv4 loopback4, port }
  let client ← Client.new
    { readTimeout := ⟨1000, by decide⟩, requestTimeout := ⟨20000, by decide⟩ }
  let size := 24 * 1024 * 1024
  let upload ← Request.new |>.method .put |>.uri! "/upload"
    |>.bytes (ByteArray.mk (Array.replicate size 120))
  let start ← IO.monoMsNow
  let outcome ← try
      let response ← client.send target upload
      pure (Except.ok (← response.body.readAll (α := String)))
    catch e => pure (.error (toString e))
  let elapsed := (← IO.monoMsNow) - start
  let atFailure ← received.get
  server.shutdownAndWait
  match outcome with
  | .ok body =>
    unless body == toString size do throw (IO.userError s!"server saw {body} bytes")
  | .error e =>
    throw (IO.userError s!"TCP upload failed after {elapsed} ms with `{e}`; the server had read \
      {atFailure} of {size} bytes then")

end TcpUploadTimeout
