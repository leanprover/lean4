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
  match decideRedirect (testOrigin "example.com") (requestHead .get basePath) true .v11 .found
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
  let connection ← Client.Connection.new mockServer (testOrigin "example.com") {}
  let request ← Request.new |>.method method |>.uri! "/x" |>.header! "Host" "example.com" |>.empty
  let promise : IO.Promise (Except Client.Error Client.TrackedResponse)
    ← IO.Promise.new
  background do
    let result ← try connection.sendTracked { request with } catch e => pure (.error (.io e))
    discard <| promise.resolve result
  let _ ← drainRequest mockClient
  mockClient.send (rawResp status (headers ++ #[("Connection", "close")]) body)
  match ← await promise.result! with
  | .error e => throw (IO.userError s!"client error: {e}")
  | .ok ⟨response, _⟩ =>
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
  let connection ← Client.Connection.new mockServer (testOrigin "example.com")
    ({ requestTimeout := ⟨700, by decide⟩ } : Client.Config)
  let request ← Request.new |>.method .get |>.uri! "/x"
    |>.header! "Host" "example.com"
    |>.header! "Connection" "Upgrade"
    |>.header! "Upgrade" "websocket" |>.empty
  let promise : IO.Promise (Except Client.Error Client.TrackedResponse)
    ← IO.Promise.new
  background do
    let result ← try connection.sendTracked { request with } catch e => pure (.error (.io e))
    discard <| promise.resolve result
  let _ ← drainRequest mockClient
  mockClient.send
    "HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n\r\n".toUTF8
  match ← await promise.result! with
  | .ok ⟨response, _⟩ =>
    response.body.close
    unless response.line.status.toCode == 101 do
      throw <| IO.userError s!"expected 101, got {response.line.status.toCode}"
  | .error .timeout =>
    throw <| IO.userError
      "a 101 response was treated as interim: the exchange only ended at requestTimeout"
  | .error _ =>
    -- A prompt protocol error is an acceptable answer; only the timeout is a defect.
    pure ()

end ClientRegressionTests
