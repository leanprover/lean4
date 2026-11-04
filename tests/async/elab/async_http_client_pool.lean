module

import Std.Http.Test.Helpers

/-! HTTP client connection pool: several connections per origin, the per-origin limit and the
requests waiting on it, connection reuse, and the release of a connection on every way an exchange
can end. -/

open Std.Async
open Std Http Internal
open Test.ClientHelpers

/-- `n` mock transports and a client whose connector hands them out in order, one per connection. -/
def poolClient (n : Nat) (config : Client.Config := {}) : Async (TestClient × Array Mock.Client) := do
  let mut clients := #[]
  let mut servers := #[]
  for _ in [0:n] do
    let (client, server) ← Mock.new
    clients := clients.push client
    servers := servers.push server
  let (testClient, _) ← mkFollowingClient servers config
  return (testClient, clients)

/-- The request line of a raw request. -/
def requestLine (bytes : ByteArray) : String :=
  ((String.fromUTF8! bytes).splitOn "\r\n").headD ""

def getReq (path : String) : Async (Request Body.Empty) :=
  Request.new |>.method .get |>.uri! path |>.empty

/-- Awaits a background send and reads its whole body. -/
def expectBody (name : String) (p : IO.Promise (Except String (Response Body.Stream))) :
    Async String := do
  match ← await p.result! with
  | .error e => throw (IO.userError s!"{name} failed: {e}")
  | .ok response => response.body.readAll (α := String)

def expectFailure (name : String) (p : IO.Promise (Except String (Response Body.Stream))) :
    Async String := do
  match ← await p.result! with
  | .error e => pure e
  | .ok response => throw (IO.userError s!"{name} unexpectedly got {response.line.status.toCode}")

def dials (client : TestClient) : Async Nat := do
  return (← client.opened.get).size

def limit (n : Nat) (h : 0 < n := by decide) : Client.Config :=
  { maxConnectionsPerOrigin := ⟨n, h⟩ }

/-- A connector that opens a fresh mock transport per connection, served by `serve` with the
connection's index, and counts the connections it opens. -/
def servingConnector (dials : IO.Ref Nat) (serve : Nat → Mock.Client → Async Unit) :
    Client.Connector := fun origin config => do
  let (mock, server) ← Mock.new
  let n ← dials.modifyGet fun n => (n, n + 1)
  background (serve n mock)
  return .ok (← Client.Connection.new server origin config)

/-- Answers every request on `mock` with `body` until the client closes the connection. -/
def serveAll (body : String) (mock : Mock.Client) : Async Unit := do
  repeat
    let request ← try some <$> drainRequest mock catch _ => pure none
    if request.isNone then break
    mock.send (rawResp "200 OK" #[("Content-Length", toString body.length)] body)

-- Three requests to one origin are in flight together, each on its own connection, and each gets the
-- response from the connection it went out on although the server answers in reverse order.
#eval show IO _ from
  runWithTimeout "concurrent same-origin requests run on separate connections" 4000 <|
  Async.block do
  let (client, mocks) ← poolClient 3
  let p0 ← sendInBackground client (← getReq "/r0")
  let p1 ← sendInBackground client (← getReq "/r1")
  let p2 ← sendInBackground client (← getReq "/r2")
  let mut lines := #[]
  for mock in mocks do
    lines := lines.push (requestLine (← drainRequest mock))
  for i in [0:3] do
    let index := 2 - i
    let path := ((lines[index]!.splitOn " ")[1]!)
    let some mock := mocks[index]? | throw (IO.userError "missing mock")
    mock.send (rawResp "200 OK" #[("Content-Length", toString path.length)] path)
  let bodies := #[← expectBody "r0" p0, ← expectBody "r1" p1, ← expectBody "r2" p2]
  unless bodies == #["/r0", "/r1", "/r2"] do
    throw (IO.userError s!"responses were crossed between requests: {bodies}")
  unless (← dials client) == 3 do
    throw (IO.userError s!"expected 3 connections, got {← dials client}")

-- At the limit, a further request waits, and goes out on the first connection given back.
#eval show IO _ from
  runWithTimeout "a request beyond the per-origin limit waits for a connection" 4000 <|
  Async.block do
  let (client, #[m0, m1]) ← poolClient 2 (limit 2) | throw (IO.userError "poolClient")
  let pa ← sendInBackground client (← getReq "/a")
  let lineA := requestLine (← drainRequest m0)
  let pb ← sendInBackground client (← getReq "/b")
  let lineB := requestLine (← drainRequest m1)
  unless lineA.startsWith "GET /a" && lineB.startsWith "GET /b" do
    throw (IO.userError s!"unexpected request lines {lineA.quote} {lineB.quote}")
  let pc ← sendInBackground client (← getReq "/c")
  IO.sleep 100
  if let some bytes ← m0.tryRecv? then
    throw (IO.userError s!"request went out on a busy connection: {(String.fromUTF8! bytes).quote}")
  if (← dials client) != 2 then
    throw (IO.userError "the pool opened a connection beyond its limit")
  m0.send (rawResp "200 OK" #[("Content-Length", "1")] "a")
  unless (← expectBody "a" pa) == "a" do throw (IO.userError "wrong body for /a")
  let lineC := requestLine (← drainRequest m0)
  unless lineC.startsWith "GET /c" do
    throw (IO.userError s!"the waiting request did not reuse the freed connection: {lineC.quote}")
  m0.send (rawResp "200 OK" #[("Content-Length", "1")] "c")
  m1.send (rawResp "200 OK" #[("Content-Length", "1")] "b")
  unless (← expectBody "c" pc) == "c" && (← expectBody "b" pb) == "b" do
    throw (IO.userError "wrong bodies for /b or /c")
  unless (← dials client) == 2 do
    throw (IO.userError s!"expected 2 connections, got {← dials client}")

-- A connection that closes after its exchange frees its place, and the waiting request opens a new one.
#eval show IO _ from
  runWithTimeout "a closed connection frees its place for a waiting request" 4000 <|
  Async.block do
  let (client, #[m0, m1]) ← poolClient 2 (limit 1) | throw (IO.userError "poolClient")
  let pa ← sendInBackground client (← getReq "/a")
  let _ ← drainRequest m0
  let pb ← sendInBackground client (← getReq "/b")
  IO.sleep 50
  m0.send (rawResp "200 OK" #[("Content-Length", "1"), ("Connection", "close")] "a")
  unless (← expectBody "a" pa) == "a" do throw (IO.userError "wrong body for /a")
  let lineB := requestLine (← drainRequest m1)
  unless lineB.startsWith "GET /b" do
    throw (IO.userError s!"the waiting request did not open a new connection: {lineB.quote}")
  m1.send (rawResp "200 OK" #[("Content-Length", "1")] "b")
  unless (← expectBody "b" pb) == "b" do throw (IO.userError "wrong body for /b")

-- A caller that reads a response to its end and sends again finds the connection back in the pool,
-- whatever framing ended the response. The connector refuses a second connection, and nothing
-- sleeps between requests.
#eval show IO _ from
  runWithTimeout "sequential requests reuse one connection" 4000 <|
  Async.block do
  let (client, #[m0]) ← poolClient 1 | throw (IO.userError "poolClient")
  let mock := m0
  let exchanges : Array (Method × String × ByteArray × String) := #[
    (.get, "/fixed", rawResp "200 OK" #[("Content-Length", "5")] "hello", "hello"),
    (.get, "/empty", rawResp "200 OK" #[("Content-Length", "0")] "", ""),
    (.head, "/head", rawResp "200 OK" #[("Content-Length", "5")] "", ""),
    (.get, "/nocontent", rawResp "204 No Content" #[] "", ""),
    (.get, "/chunked", rawResp "200 OK" #[("Transfer-Encoding", "chunked")]
      "3\r\nabc\r\n0\r\n\r\n", "abc"),
    (.get, "/last", rawResp "200 OK" #[("Content-Length", "2")] "ok", "ok")
  ]
  for (method, path, response, expected) in exchanges do
    let request ← Request.new |>.method method |>.uri! path |>.empty
    let p ← sendInBackground client request
    let line := requestLine (← drainRequest mock)
    unless line.startsWith s!"{method} {path}" do
      throw (IO.userError s!"expected {path} on the pooled connection, got {line.quote}")
    mock.send response
    let body ← expectBody path p
    unless body == expected do
      throw (IO.userError s!"{path}: expected {expected.quote}, got {body.quote}")

-- Each origin keeps its own connection: a request to another origin neither closes nor replaces the
-- first origin's, and the first origin's next request reuses it.
#eval show IO _ from
  runWithTimeout "different origins keep their own connections" 4000 <|
  Async.block do
  let (client, #[m0, m1]) ← poolClient 2 | throw (IO.userError "poolClient")
  let pa ← sendInBackground client (← getReq "/a1")
  let _ ← drainRequest m0
  m0.send (rawResp "200 OK" #[("Content-Length", "2")] "a1")
  unless (← expectBody "a1" pa) == "a1" do throw (IO.userError "wrong body for /a1")

  let pb : IO.Promise (Except String (Response Body.Stream)) ← IO.Promise.new
  let requestB ← getReq "/b1"
  background do
    let result ← try pure (.ok (← client.client.send (origin "other.example") requestB))
      catch e => pure (.error (toString e))
    discard <| pb.resolve result
  let lineB := requestLine (← drainRequest m1)
  unless lineB.startsWith "GET /b1" do
    throw (IO.userError s!"the second origin did not get its own connection: {lineB.quote}")
  m1.send (rawResp "200 OK" #[("Content-Length", "2")] "b1")
  unless (← expectBody "b1" pb) == "b1" do throw (IO.userError "wrong body for /b1")

  let pa2 ← sendInBackground client (← getReq "/a2")
  let lineA2 := requestLine (← drainRequest m0)
  unless lineA2.startsWith "GET /a2" do
    throw (IO.userError s!"the first origin's connection was not reused: {lineA2.quote}")
  m0.send (rawResp "200 OK" #[("Content-Length", "2")] "a2")
  unless (← expectBody "a2" pa2) == "a2" do throw (IO.userError "wrong body for /a2")
  unless (← dials client) == 2 do
    throw (IO.userError s!"expected 2 connections, got {← dials client}")

-- A response body nobody reads holds only its own connection: the next request to the same origin
-- goes out at once on another one instead of waiting for the first request's deadline.
#eval show IO _ from
  runWithTimeout "an unread body holds only its own connection" 4000 <|
  Async.block do
  let (client, #[m0, m1]) ← poolClient 2 | throw (IO.userError "poolClient")
  let pa ← sendInBackground client (← getReq "/a")
  let _ ← drainRequest m0
  m0.send (rawResp "200 OK" #[("Content-Length", "5")] "hello")
  let responseA ← match ← await pa.result! with
    | .ok response => pure response
    | .error e => throw (IO.userError s!"/a failed: {e}")
  let pb ← sendInBackground client (← getReq "/b")
  let lineB := requestLine (← drainRequest m1)
  unless lineB.startsWith "GET /b" do
    throw (IO.userError s!"unexpected request line {lineB.quote}")
  m1.send (rawResp "200 OK" #[("Content-Length", "1")] "b")
  unless (← expectBody "b" pb) == "b" do throw (IO.userError "wrong body for /b")
  responseA.body.close

-- One request's cross-origin redirect does not disturb another request to the redirecting origin
-- that is in flight at the same time.
#eval show IO _ from
  runWithTimeout "a redirect elsewhere does not abort a concurrent same-origin request" 4000 <|
  Async.block do
  let (client, #[m0, m1, m2]) ← poolClient 3 | throw (IO.userError "poolClient")
  let pGet ← sendInBackground client (← getReq "/x")
  let _ ← drainRequest m0
  let post ← Request.new |>.method .post |>.uri! "/y" |>.text "payload"
  let pPost ← sendInBackground client post
  let linePost := requestLine (← drainRequest m1)
  unless linePost.startsWith "POST /y" do
    throw (IO.userError s!"unexpected request line {linePost.quote}")
  m0.send (rawResp "302 Found"
    #[("Location", "http://other.example/z"), ("Content-Length", "0")] "")
  let lineZ := requestLine (← drainRequest m2)
  unless lineZ.startsWith "GET /z" do
    throw (IO.userError s!"the redirect was not followed on a new connection: {lineZ.quote}")
  m2.send (rawResp "200 OK" #[("Content-Length", "1")] "z")
  m1.send (rawResp "201 Created" #[("Content-Length", "1")] "y")
  unless (← expectBody "redirected GET" pGet) == "z" do
    throw (IO.userError "wrong body for the redirected GET")
  unless (← expectBody "POST" pPost) == "y" do
    throw (IO.userError "wrong body for the POST")

-- `Client.close` aborts the exchange in flight, fails the request waiting for a connection, and
-- closes the transport.
#eval show IO _ from
  runWithTimeout "Client.close aborts in-flight and waiting requests" 4000 <|
  Async.block do
  let (client, #[m0]) ← poolClient 1 (limit 1) | throw (IO.userError "poolClient")
  let pa ← sendInBackground client (← getReq "/a")
  let _ ← drainRequest m0
  let pb ← sendInBackground client (← getReq "/b")
  IO.sleep 50
  client.client.close
  discard <| expectFailure "in-flight request" pa
  discard <| expectFailure "waiting request" pb
  if let some bytes ← m0.recv? then
    throw (IO.userError s!"a request was written after close: {(String.fromUTF8! bytes).quote}")

-- A redirect whose body outgrows `intermediateBodyDrainLimit` is followed at once on a new connection
-- rather than after the server finishes a body that, here, never ends.
#eval show IO _ from
  runWithTimeout "an oversized redirect body is abandoned with its connection" 3000 <|
  Async.block do
  let (client, #[m0, m1]) ← poolClient 2 { intermediateBodyDrainLimit := 16 } | throw (IO.userError "poolClient")
  let p ← sendInBackground client (← getReq "/start")
  let _ ← drainRequest m0
  let filler := String.ofList (List.replicate 64 'x')
  m0.send (rawResp "302 Found"
    #[("Location", "/next"), ("Transfer-Encoding", "chunked")] s!"40\r\n{filler}\r\n")
  let line := requestLine (← drainRequest m1)
  unless line.startsWith "GET /next" do
    throw (IO.userError s!"the redirect did not go out on a new connection: {line.quote}")
  m1.send (rawResp "200 OK" #[("Content-Length", "2")] "ok")
  unless (← expectBody "redirect" p) == "ok" do throw (IO.userError "wrong final body")
  if let some bytes ← m0.recv? then
    throw (IO.userError s!"the abandoned connection carried another request: {(String.fromUTF8! bytes).quote}")

-- A request a middleware fails before it reaches the connection gives the connection back unused.
#eval show IO _ from
  runWithTimeout "a request refused by a middleware leaves its connection usable" 4000 <|
  Async.block do
  let (mock, server) ← Mock.new
  let dialled ← IO.mkRef 0
  let connect : Client.Connector := fun origin config => do
    dialled.modify (· + 1)
    if (← dialled.get) > 1 then throw (IO.userError "opened a second connection")
    return .ok (← Client.Connection.new server origin config)
  let refuse : Client.Middleware := fun _ req next =>
    if (toString req.line.uri).startsWith "/refused" then
      pure (.error (.invalidRequest "refused by middleware"))
    else
      next req
  let client ← Client.new (limit 1) connect (maxRetries := 0) (middlewares := #[refuse])
  let target := origin "example.com"
  match ← client.trySend target (← getReq "/refused") with
  | .error (.invalidRequest _) => pure ()
  | .error e => throw (IO.userError s!"unexpected error {e}")
  | .ok _ => throw (IO.userError "the refused request succeeded")
  let p : IO.Promise (Except Client.Error (Response Body.Stream)) ← IO.Promise.new
  let request ← getReq "/allowed"
  background do discard <| p.resolve (← client.trySend target request)
  let line := requestLine (← drainRequest mock)
  unless line.startsWith "GET /allowed" do
    throw (IO.userError s!"unexpected request line {line.quote}")
  mock.send (rawResp "200 OK" #[("Content-Length", "2")] "ok")
  match ← await p.result! with
  | .ok response =>
    unless (← response.body.readAll (α := String)) == "ok" do throw (IO.userError "wrong body")
  | .error e => throw (IO.userError s!"the allowed request failed: {e}")

-- A failed exchange gives up its place under the limit, so the next request is not left waiting.
#eval show IO _ from
  runWithTimeout "a failed exchange frees its place" 4000 <|
  Async.block do
  let (client, #[m0, m1]) ← poolClient 2 (limit 1) | throw (IO.userError "poolClient")
  let pa ← sendInBackground client (← getReq "/a")
  let _ ← drainRequest m0
  m0.send "NOT HTTP AT ALL\r\n\r\n".toUTF8
  discard <| expectFailure "malformed response" pa
  let pb ← sendInBackground client (← getReq "/b")
  let line := requestLine (← drainRequest m1)
  unless line.startsWith "GET /b" do
    throw (IO.userError s!"unexpected request line {line.quote}")
  m1.send (rawResp "200 OK" #[("Content-Length", "1")] "b")
  unless (← expectBody "b" pb) == "b" do throw (IO.userError "wrong body for /b")

-- A connector failure gives up the place it was reserved, so the next request can dial.
#eval show IO _ from
  runWithTimeout "a failed connect frees its place" 4000 <|
  Async.block do
  let (mock, server) ← Mock.new
  let calls ← IO.mkRef 0
  let connect : Client.Connector := fun origin config => do
    calls.modify (· + 1)
    if (← calls.get) == 1 then return .error (.connect "refused")
    return .ok (← Client.Connection.new server origin config)
  let client ← Client.new (limit 1) connect (maxRetries := 0)
  let target := origin "example.com"
  match ← client.trySend target (← getReq "/a") with
  | .error (.connect _) => pure ()
  | .error e => throw (IO.userError s!"unexpected error {e}")
  | .ok _ => throw (IO.userError "the first request should have failed to connect")
  let p : IO.Promise (Except Client.Error (Response Body.Stream)) ← IO.Promise.new
  let request ← getReq "/b"
  background do discard <| p.resolve (← client.trySend target request)
  let line := requestLine (← drainRequest mock)
  unless line.startsWith "GET /b" do
    throw (IO.userError s!"unexpected request line {line.quote}")
  mock.send (rawResp "200 OK" #[("Content-Length", "1")] "b")
  match ← await p.result! with
  | .ok response =>
    unless (← response.body.readAll (α := String)) == "b" do throw (IO.userError "wrong body")
  | .error e => throw (IO.userError s!"the second request failed: {e}")

-- An exception from user code inside an exchange (here a cookie handler) closes the connection
-- instead of leaving it checked out, so with one connection per origin the next request still goes.
#eval show IO _ from
  runWithTimeout "an exception from a cookie handler does not leak its connection" 4000 <|
  Async.block do
  let loads ← IO.mkRef 0
  let handler : Client.CookieHandler := {
    load := fun _ _ => do
      loads.modify (· + 1)
      if (← loads.get) == 1 then throw (IO.userError "cookie jar unavailable")
      return #[]
    store := fun _ _ _ => pure () }
  let dials ← IO.mkRef 0
  let config := { limit 1 with cookieHandler := some handler, keepAliveTimeout := ⟨60000, by decide⟩ }
  let client ← Client.new config (servingConnector dials fun _ => serveAll "ok") (maxRetries := 0)
  let target := origin "example.com"
  match ← client.trySend target (← getReq "/a") with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "the first request should fail in its cookie handler")
  match ← client.trySend target (← getReq "/b") with
  | .ok response =>
    unless (← response.body.readAll (α := String)) == "ok" do throw (IO.userError "wrong body for /b")
  | .error e => throw (IO.userError s!"the second request failed: {e}")

-- A middleware that calls through again (refreshing credentials after a 401) gets the connection
-- back as soon as the first exchange ends, instead of waiting for it to time out.
#eval show IO _ from
  runWithTimeout "a middleware that calls next twice reuses the connection" 4000 <|
  Async.block do
  let refresh : Client.Middleware := fun _ req next => do
    match ← next req with
    | .ok response =>
      if response.line.status == .unauthorized then
        discard <| response.body.readAll (α := ByteArray)
        next req
      else
        pure (.ok response)
    | .error e => pure (.error e)
  let answered ← IO.mkRef 0
  let serve : Nat → Mock.Client → Async Unit := fun _ mock => do
    repeat
      let request ← try some <$> drainRequest mock catch _ => pure none
      if request.isNone then break
      if (← answered.modifyGet fun n => (n, n + 1)) == 0 then
        mock.send (rawResp "401 Unauthorized" #[("Content-Length", "0")] "")
      else
        mock.send (rawResp "200 OK" #[("Content-Length", "2")] "ok")
  let dials ← IO.mkRef 0
  let client ← Client.new (limit 1) (servingConnector dials serve) (maxRetries := 0)
    (middlewares := #[refresh])
  let start ← IO.monoMsNow
  match ← client.trySend (origin "example.com") (← getReq "/api") with
  | .ok response =>
    unless (← response.body.readAll (α := String)) == "ok" do throw (IO.userError "wrong body")
  | .error e => throw (IO.userError s!"the request failed: {e}")
  let elapsed := (← IO.monoMsNow) - start
  unless (← dials.get) == 1 do
    throw (IO.userError s!"expected one connection, got {← dials.get}")
  if elapsed > 1000 then
    throw (IO.userError s!"the second call waited {elapsed} ms for the first exchange's connection")

-- With retries on (the default), `Client.close` still ends the requests it interrupts: neither the
-- one in flight nor the one waiting for a connection is sent again.
#eval show IO _ from
  runWithTimeout "Client.close is not undone by a retry" 4000 <|
  Async.block do
  let seen : IO.Promise Unit ← IO.Promise.new
  let silent : Nat → Mock.Client → Async Unit := fun _ mock => do
    discard <| drainRequest mock
    seen.resolve ()
  let dials ← IO.mkRef 0
  let client ← Client.new (limit 1) (servingConnector dials silent)
  let target := origin "example.com"
  let inFlight ← async (t := AsyncTask) (client.trySend target (← getReq "/a"))
  await seen.result!
  let waiting ← async (t := AsyncTask) (client.trySend target (← getReq "/b"))
  IO.sleep 50
  client.close
  for (name, task) in #[("in-flight", inFlight), ("waiting", waiting)] do
    match ← await task with
    | .ok _ => throw (IO.userError s!"the {name} request succeeded after Client.close")
    | .error _ => pure ()
  IO.sleep 50
  unless (← dials.get) == 1 do
    throw (IO.userError s!"a request was retried after Client.close: {← dials.get} connections")

-- A retry goes out on a new connection: the other idle connection may have gone stale the same way
-- as the one that failed.
#eval show IO _ from
  runWithTimeout "a retry opens a fresh connection instead of reusing an idle one" 4000 <|
  Async.block do
  let serveOnceThenDrop : Mock.Client → Async Unit := fun mock => do
    discard <| drainRequest mock
    mock.send (rawResp "200 OK" #[("Content-Length", "2")] "ok")
    discard <| drainRequest mock
    mock.close
  let dials ← IO.mkRef 0
  let serve : Nat → Mock.Client → Async Unit := fun n mock =>
    if n < 2 then serveOnceThenDrop mock else serveAll "fresh" mock
  let client ← Client.new {} (servingConnector dials serve) (maxRetries := 1)
  let target := origin "example.com"
  let first ← async (t := AsyncTask) (client.trySend target (← getReq "/a"))
  let second ← async (t := AsyncTask) (client.trySend target (← getReq "/b"))
  for task in #[first, second] do
    match ← await task with
    | .ok response => discard <| response.body.readAll (α := String)
    | .error e => throw (IO.userError s!"warm-up request failed: {e}")
  match ← client.trySend target (← getReq "/c") with
  | .ok response =>
    unless (← response.body.readAll (α := String)) == "fresh" do
      throw (IO.userError "the retry was not answered by a new connection")
  | .error e => throw (IO.userError s!"the retried GET failed: {e} after {← dials.get} connections")

-- A connection that finishes opening after `Client.close` is closed rather than used.
#eval show IO _ from
  runWithTimeout "a connection opened after Client.close is not used" 4000 <|
  Async.block do
  let (mock, server) ← Mock.new
  let entered : IO.Promise Unit ← IO.Promise.new
  let gate : IO.Promise Unit ← IO.Promise.new
  let connect : Client.Connector := fun origin config => do
    entered.resolve ()
    await gate.result!
    return .ok (← Client.Connection.new server origin config)
  let client ← Client.new {} connect (maxRetries := 0)
  let pending ← async (t := AsyncTask) (client.trySend (origin "example.com") (← getReq "/late"))
  await entered.result!
  client.close
  gate.resolve ()
  match ← await pending with
  | .ok _ => throw (IO.userError "the request went out on a connection opened after Client.close")
  | .error _ => pure ()
  if let some bytes ← mock.tryRecv? then
    unless bytes.isEmpty do
      throw (IO.userError s!"a request was written after Client.close: {(String.fromUTF8! bytes).quote}")

-- A request with an empty body that the loop has not yet seen end still finds the connection idle
-- once its response has been read.
#eval show IO _ from
  runWithTimeout "sequential requests with an empty text body reuse one connection" 4000 <|
  Async.block do
  let (client, #[m0]) ← poolClient 1 | throw (IO.userError "poolClient")
  for i in [0:30] do
    let request ← Request.new |>.method .get |>.uri! s!"/{i}" |>.text ""
    let p ← sendInBackground client request
    let _ ← drainRequest m0
    m0.send (rawResp "200 OK" #[("Content-Length", "2")] "ok")
    unless (← expectBody s!"/{i}" p) == "ok" do throw (IO.userError s!"wrong body for /{i}")

-- A request that provably never reached a peer is sent again whatever its method: here a `POST`
-- whose first connection could not be opened.
#eval show IO _ from
  runWithTimeout "a POST that never left the client is retried" 4000 <|
  Async.block do
  let (mock, server) ← Mock.new
  let calls ← IO.mkRef 0
  let connect : Client.Connector := fun origin config => do
    calls.modify (· + 1)
    if (← calls.get) == 1 then return .error (.connect "refused")
    return .ok (← Client.Connection.new server origin config)
  let client ← Client.new {} connect (maxRetries := 1)
  let request ← Request.new |>.method .post |>.uri! "/orders" |>.text "item=1"
  let p : IO.Promise (Except Client.Error (Response Body.Stream)) ← IO.Promise.new
  background do discard <| p.resolve (← client.trySend (origin "example.com") request)
  let line := requestLine (← drainRequest mock)
  unless line.startsWith "POST /orders" do
    throw (IO.userError s!"unexpected request line {line.quote}")
  mock.send (rawResp "201 Created" #[("Content-Length", "2")] "ok")
  match ← await p.result! with
  | .ok response =>
    unless (← response.body.readAll (α := String)) == "ok" do throw (IO.userError "wrong body")
  | .error e => throw (IO.userError s!"the POST was not retried: {e}")

/-- A replayable body whose rewind fails. -/
structure FailingRewind where
  inner : Body.Full

instance : Body FailingRewind where
  recv b := Body.recv b.inner
  recvSelector b := Body.recvSelector b.inner
  close b := Body.close b.inner
  isClosed b := Body.isClosed b.inner
  tryRecv b := Body.tryRecv b.inner
  getKnownSize b := Body.getKnownSize b.inner
  setKnownSize b size := Body.setKnownSize b.inner size

instance : Coe FailingRewind Body.Any where
  coe b := { Body.Any.ofBody b with reset? := some (throw (IO.userError "rewind failed")) }

-- A body that fails to rewind for a retry fails the request with a typed error rather than an
-- exception thrown out of `trySend`.
#eval show IO _ from
  runWithTimeout "a failing rewind is reported as a typed error" 4000 <|
  Async.block do
  let calls ← IO.mkRef 0
  let connect : Client.Connector := fun _ _ => do
    calls.modify (· + 1)
    return .error (.connect "refused")
  let client ← Client.new {} connect (maxRetries := 1)
  let body : FailingRewind := { inner := ← Body.Full.ofString "data" }
  let request := Request.new |>.method .put |>.uri! "/doc" |>.body body
  match ← client.trySend (origin "example.com") request with
  | .error (.io _) => pure ()
  | .error e => throw (IO.userError s!"expected an io error, got {e}")
  | .ok _ => throw (IO.userError "the request succeeded")
