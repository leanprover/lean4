module

import Std.Http.Test.Helpers

/-!
Regression tests for HTTP client defects.
-/

open Std.Async
open Std Http Internal
open Test.ClientHelpers
open Std.Http.Protocol.H1

namespace ClientRegressionTests

private def assertEq (what actual expected : String) : IO Unit := do
  unless actual == expected do
    throw <| IO.userError s!"{what}: expected {expected.quote}, got {actual.quote}"

-- ============================================================
-- Section 1 — origin-form is never empty (RFC 9112 §3.2.1)
-- ============================================================

private def emptyPath : URI.Path := { segments := #[], absolute := false }

#eval show IO Unit from do
  -- Control: a non-empty path is rendered unchanged, so this pins the empty case alone.
  assertEq "origin-form with a path"
    (toString (RequestTarget.originForm { segments := #[.encode "a"], absolute := true } none)) "/a"

  assertEq "origin-form with an empty path"
    (toString (RequestTarget.originForm emptyPath none)) "/"

  assertEq "origin-form with an empty path and a query"
    (toString (RequestTarget.originForm emptyPath (some #[(.encode "q", some (.encode "1"))])))
    "/?q=1"

-- ============================================================
-- Section 2 — dot segments are removed from every reference form (RFC 3986 §5.2.2)
-- ============================================================

private def testOrigin (host : String) (port : UInt16 := 80) : URI.Origin :=
  let scheme := URI.Scheme.ofString! "http"
  match URI.DomainName.ofString? host with
  | some domain => { scheme, host := .name domain, port }
  | none => { scheme, host := default, port }

private def requestHead (method : Method) (path : String) : Request.Head :=
  (Request.new |>.method method |>.uri! path |>.header! "Host" "example.com").line

private def locationHeaders (location : String) : Headers :=
  match Header.Value.ofString? location with
  | some value => (∅ : Headers).insert .location value
  | none => ∅

/-- The request target `decideRedirect` plans for a 302 to `location`, from `basePath`. -/
private def plannedTarget (location : String) (basePath : String := "/start") : String :=
  match decideRedirect (testOrigin "example.com") (requestHead .get basePath) true false .v11 .found
      (locationHeaders location) with
  | .done => "<not followed>"
  | .follow plan => toString plan.target

#eval show IO Unit from do
  -- Control: the bare-path branch already resolved dot segments, so this pins the expectation.
  assertEq "path-only Location" (plannedTarget "/a/../../etc/passwd") "/etc/passwd"

  assertEq "absolute Location" (plannedTarget "http://example.com/a/../../etc/passwd")
    "/etc/passwd"

  assertEq "cross-origin absolute Location" (plannedTarget "http://other.example/x/../../y")
    "http://other.example/y"

  assertEq "cross-origin protocol-relative Location" (plannedTarget "//other.example/x/../y")
    "http://other.example/y"

#eval show IO Unit from do
  assertEq "absolute Location with an empty path" (plannedTarget "http://example.com") "/"
  assertEq "protocol-relative Location with an empty path" (plannedTarget "//example.com") "/"
  assertEq "absolute Location with only a query" (plannedTarget "http://example.com?q=1") "/?q=1"

-- ============================================================
-- Section 3 — a trailing "." or ".." keeps the trailing slash (RFC 3986 §5.2.4, §5.4.1)
-- ============================================================

private def normalized (path : String) : String :=
  match RequestTarget.parse? path with
  | some (.originForm p _) => toString p.normalize
  | _ => "<unparseable>"

#eval show IO Unit from do
  -- Control: an interior dot segment is removed outright, with no slash to preserve.
  assertEq "interior \".\"" (normalized "/a/./b") "/a/b"
  -- The worked example from RFC 3986 §5.2.4 itself.
  assertEq "RFC 5.2.4 example" (normalized "/a/b/c/./../../g") "/a/g"

  assertEq "trailing \".\"" (normalized "/a/b/c/.") "/a/b/c/"
  assertEq "trailing \"..\"" (normalized "/a/b/..") "/a/"
  -- Popping past the root leaves the root itself, not an empty path.
  assertEq "\"..\" past the root" (normalized "/a/b/../../..") "/"

#eval show IO Unit from do
  -- Control: `../` carries its own trailing empty segment, so it already resolved correctly. It
  -- shares every step with the cases below except the final-segment rewrite.
  assertEq "control (\"../\")" (plannedTarget "../" "/a/b/c") "/a/"

  -- RFC 3986 §5.4.1: base `/b/c/d;p`, reference `"."` → `/b/c/`.
  assertEq "\".\"" (plannedTarget "." "/a/b/c") "/a/b/"
  -- RFC 3986 §5.4.1: base `/b/c/d;p`, reference `".."` → `/b/`.
  assertEq "\"..\"" (plannedTarget ".." "/a/b/c") "/a/"
  -- Only the final segment gets the rewrite: the first `..` just pops a segment.
  assertEq "\"../..\"" (plannedTarget "../.." "/a/b/c/d") "/a/"

-- ============================================================
-- Section 4 — a bodyless response must not advertise a body (RFC 9112 §6.3)
-- ============================================================

/-- The known size the client publishes for a response, together with what the caller reads. -/
private def responseSizeAndBody (method : Method) (status : String)
    (headers : Array (String × String)) (body : String := "") :
    Async (Option Body.Length × String) := do
  let (mockClient, mockServer) ← Mock.new
  let connection ← Client.Connection.new mockServer {}
  let request ← Request.new |>.method method |>.uri! "/x" |>.header! "Host" "example.com" |>.empty
  let promise : IO.Promise (Except Client.Error (Response Body.Stream × IO.Promise (Except Client.Error Unit)))
    ← IO.Promise.new
  background do
    let result ← try connection.sendTracked { request with } catch e => pure (.error (.io e))
    discard <| promise.resolve result
  let _ ← drainRequest mockClient
  mockClient.send (rawResp status (headers ++ #[("Connection", "close")]) body)
  match ← await promise.result! with
  | .error e => throw (IO.userError s!"client error: {e}")
  | .ok (response, _) =>
    let size ← response.body.getKnownSize
    let received : String ← response.body.readAll
    pure (size, received)

private def assertAdvertisesNoBody (what : String) (result : Option Body.Length × String) :
    IO Unit := do
  let (size, body) := result
  unless body.isEmpty do
    throw <| IO.userError s!"{what}: expected an empty body, read {body.quote}"
  match size with
  | none | some (.fixed 0) => pure ()
  | some other =>
    throw <| IO.userError s!"{what}: body advertises {repr other} but yields no bytes"

#eval show IO _ from
  runWithTimeout "a bodyless response does not advertise a Content-Length" 6000 <| Async.block do
  -- Control: a status that does carry content still reports its size, so the guard is not
  -- suppressing every known size.
  let (size, body) ← responseSizeAndBody .get "200 OK" #[("Content-Length", "2")] "ok"
  unless body == "ok" do
    throw <| IO.userError s!"control: expected to read the 200's body, got {body.quote}"
  unless size == some (.fixed 2) do
    throw <| IO.userError s!"control: a 200 must report its Content-Length, got {repr size}"

  assertAdvertisesNoBody "HEAD 200 with Content-Length: 100"
    (← responseSizeAndBody .head "200 OK" #[("Content-Length", "100")])
  assertAdvertisesNoBody "204 with Content-Length: 100"
    (← responseSizeAndBody .get "204 No Content" #[("Content-Length", "100")])
  assertAdvertisesNoBody "304 with Content-Length: 100"
    (← responseSizeAndBody .get "304 Not Modified" #[("Content-Length", "100")])

-- ============================================================
-- Section 5 — 101 Switching Protocols ends the exchange (RFC 9110 §15.2.2)
-- ============================================================

#eval show IO _ from
  runWithTimeout "101 Switching Protocols ends the exchange" 5000 <| Async.block do
  let (mockClient, mockServer) ← Mock.new
  let connection ← Client.Connection.new mockServer
    ({ requestTimeout := ⟨700, by decide⟩ } : Client.Config)
  let request ← Request.new |>.method .get |>.uri! "/x"
    |>.header! "Host" "example.com"
    |>.header! "Connection" "Upgrade"
    |>.header! "Upgrade" "websocket" |>.empty
  let promise : IO.Promise (Except Client.Error (Response Body.Stream × IO.Promise (Except Client.Error Unit)))
    ← IO.Promise.new
  background do
    let result ← try connection.sendTracked { request with } catch e => pure (.error (.io e))
    discard <| promise.resolve result
  let _ ← drainRequest mockClient
  mockClient.send
    "HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n\r\n".toUTF8
  match ← await promise.result! with
  | .ok (response, _) =>
    response.body.close
    unless response.line.status.toCode == 101 do
      throw <| IO.userError s!"expected 101, got {response.line.status.toCode}"
  | .error .timeout =>
    throw <| IO.userError
      "a 101 response was treated as interim: the exchange only ended at requestTimeout"
  | .error _ =>
    -- A prompt protocol error is an acceptable answer; only the timeout is a defect.
    pure ()

-- ============================================================
-- Section 6 — evicting a pooled connection must not abort its exchange
-- ============================================================

/-- A connector handing out `servers` in order; opening more than there are fails the test. -/
private def mockConnector (servers : Array Mock.Server) (opened : IO.Ref Nat) :
    Client.Connector := fun _ host _ config => do
  let index ← opened.modifyGet fun n => (n, n + 1)
  let some server := servers[index]?
    | return .error (.connect s!"the pool opened more than {servers.size} connections (for {host})")
  return .ok (← Client.Connection.new server config)

private def poolRequest : Async (Request Body.Empty) :=
  Request.new |>.method .get |>.uri! "/x" |>.header! "Host" "example.com" |>.empty

#eval show IO _ from
  runWithTimeout "an origin swap does not kill another origin's in-flight response" 8000 <|
  Async.block do
  let (clientA, serverA) ← Mock.new
  let (clientB, serverB) ← Mock.new
  let opened ← IO.mkRef 0
  -- Retries disabled: a retry would paper over the teardown by re-sending the request.
  let client ← Client.new {} (mockConnector #[serverA, serverB] opened) 0
  let request ← poolRequest

  -- A gets its head and half its body; the caller still holds an open stream.
  let resultA ← IO.Promise.new
  background do discard <| resultA.resolve (← client.trySend (testOrigin "a.example") request)
  let _ ← drainRequest clientA
  clientA.send "HTTP/1.1 200 OK\r\nContent-Length: 10\r\n\r\n01234".toUTF8
  let responseA ← match ← await resultA.result! with
    | .error e => throw (IO.userError s!"request A failed: {e}")
    | .ok response => pure response

  -- B targets a different origin, so the pool evicts A's connection.
  let resultB ← IO.Promise.new
  background do discard <| resultB.resolve (← client.trySend (testOrigin "b.example") request)
  let _ ← drainRequest clientB
  clientB.send (rawResp "200 OK" #[("Content-Length", "2"), ("Connection", "keep-alive")] "ok")
  match ← await resultB.result! with
  | .error e => throw (IO.userError s!"request B failed: {e}")
  | .ok response => let _ : String ← response.body.readAll; pure ()

  -- A's remaining body must still arrive.
  background do
    try clientA.send "56789".toUTF8 catch _ => pure ()
  let bodyA : String ← try responseA.body.readAll
    catch e => throw (IO.userError s!"the origin swap tore down A's in-flight response: {e}")
  unless bodyA == "0123456789" do
    throw <| IO.userError s!"A's response body was truncated to {bodyA.quote}"

#eval show IO _ from
  runWithTimeout "concurrent cross-origin pool requests both succeed" 8000 <| Async.block do
  let mocks ← (Array.range 4).mapM fun _ => Mock.new
  let opened ← IO.mkRef 0
  let client ← Client.new {} (mockConnector (mocks.map (·.2)) opened) 1
  let request ← poolRequest

  -- Every mock answers every request it sees, so the test never depends on which connection the
  -- pool happens to hand a given request.
  for (mockClient, _) in mocks do
    background do
      repeat
        let _ ← drainRequest mockClient
        mockClient.send
          (rawResp "200 OK" #[("Content-Length", "2"), ("Connection", "keep-alive")] "ok")

  let resultA ← IO.Promise.new
  let resultB ← IO.Promise.new
  background do discard <| resultA.resolve (← client.trySend (testOrigin "a.example") request)
  background do discard <| resultB.resolve (← client.trySend (testOrigin "b.example") request)
  for (label, result) in [("a.example", resultA), ("b.example", resultB)] do
    match ← await result.result! with
    | .error e => throw (IO.userError s!"the concurrent request to {label} failed: {e}")
    | .ok response =>
      let _ : String ← try response.body.readAll
        catch e =>
          throw (IO.userError s!"reading the concurrent response from {label} failed: {e}")
      pure ()

end ClientRegressionTests
