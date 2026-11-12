module

import Std.Http.Test.Helpers

/-!
# Redirect decisions

`Std.Http.Protocol.H1.decideRedirect`: when a redirect is followed or terminal, how the method and
body are chosen, how the target is rewritten, and how fields are scrubbed. RFC 9110 §15.4, §7.6.1,
§9.3.6; RFC 9112 §3.2; RFC 3986 §5.2.2. Regressions: #16036.
-/

open Std Http
open Std.Http.Protocol.H1
open Std.Http.Internal.Test

/-- Base origin all tests redirect away from: `http://example.com/a/b` (port 80). -/
private def base : URI := URI.parse! "http://example.com/a/b"

private def origin : URI.Origin :=
  { scheme := base.scheme, host := base.host?.get!, port := base.port }

private def mkReq (method : Method) (headers : Headers := .empty) (version : Version := .v11) :
    Request.Head :=
  { method, version, uri := base.originTarget, headers }

private def withLocation (loc : String) : Headers :=
  Headers.empty.insert .location (Header.Value.ofString! loc)

private def credHeaders : Headers :=
  Headers.empty
    |>.insert .host (Header.Value.ofString! "example.com")
    |>.insert .authorization (Header.Value.ofString! "Bearer secret")
    |>.insert .cookie (Header.Value.ofString! "sid=abc")

private def contentHeaders : Headers :=
  Headers.empty
    |>.insert .contentType (Header.Value.ofString! "text/plain")
    |>.insert .contentLength (Header.Value.ofString! "3")

private def isDone : RedirectOutcome → Bool
  | .done => true
  | .follow _ => false

private def isEmptyBody : RedirectBodyAction → Bool
  | .empty => true
  | .replay => false

private def isReplayBody : RedirectBodyAction → Bool
  | .replay => true
  | .empty => false

/-- Fails unless `outcome` is a followed plan that satisfies `ok`. -/
private def expectPlan (outcome : RedirectOutcome) (ok : RedirectPlan → Bool) : IO Unit :=
  match outcome with
  | .follow p => ensure (ok p) s!"unexpected plan: method {p.method}, target {toString p.target}, crossOrigin {p.isCrossOrigin}"
  | .done => throw <| IO.userError "the redirect was not followed"

private def targetFor (requestTarget location : String) : String :=
  let req : Request.Head := { method := .get, version := .v11, uri := RequestTarget.parse! requestTarget }
  match decideRedirect origin req false .found (withLocation location) with
  | .follow p => toString p.target
  | .done => "no plan"

/-- A CONNECT target is the authority to tunnel to (RFC 9110 §9.3.6). -/
private def connectReq : Request.Head :=
  { method := .connect, version := .v11, uri := RequestTarget.parse! "example.com:443" }

/-! ## Terminal responses (RFC 9110 §15.4) -/

#eval checkCases "Terminal responses (`.done`)" #[
    ("A non-3xx status is never a redirect", mkReq .get, false, Status.ok, withLocation "/x"),
    ("A 3xx status with no `Location` header cannot be followed", mkReq .get, false, .found, Headers.empty),
    ("SSRF guard: a `Location` resolving to a non-http(s) scheme is rejected", mkReq .get, false, .found,
      withLocation "file:///etc/passwd"),
    ("305 Use Proxy", mkReq .get, false, .useProxy, withLocation "/x"),
    ("306 Unused", mkReq .get, false, .unused, withLocation "/x"),
    ("304 Not Modified", mkReq .get, false, .notModified, withLocation "/x"),
    ("300 Multiple Choices", mkReq .get, false, .multipleChoices, withLocation "/x"),
    ("301 PUT whose body cannot be replayed", mkReq .put, false, .movedPermanently, withLocation "/x"),
    ("302 PATCH whose body cannot be replayed", mkReq .patch, false, .found, withLocation "/x"),
    ("307 POST with a non-replayable body", mkReq .post, false, .temporaryRedirect, withLocation "/x"),
    ("CONNECT, 301", connectReq, true, .movedPermanently, withLocation "/x"),
    ("CONNECT, 302", connectReq, true, .found, withLocation "/x"),
    ("CONNECT, 303", connectReq, true, .seeOther, withLocation "/x"),
    ("CONNECT, 307", connectReq, true, .temporaryRedirect, withLocation "/x"),
    ("CONNECT, 308", connectReq, true, .permanentRedirect, withLocation "/x"),
    ("CONNECT, 302 to another authority", connectReq, true, .found, withLocation "http://other.com:443")
  ] fun (label, req, replayable, status, headers) =>
    ensure (isDone (decideRedirect origin req replayable status headers)) s!"{label}: the redirect was followed"

/-! ## Method and body (RFC 9110 §15.4.2–§15.4.9) -/

#eval checkCases "Followed redirects: method selection" #[
    ("Same-origin 302 on GET: method preserved, target rewritten to origin-form, empty body",
      expectPlan (decideRedirect origin (mkReq .get) false .found (withLocation "/next")) fun p =>
        p.method == .get && !p.isCrossOrigin && toString p.target == "/next" && isEmptyBody p.bodyAction),
    ("303 See Other downgrades POST to GET with an empty body",
      expectPlan (decideRedirect origin (mkReq .post) false .seeOther (withLocation "/next")) fun p =>
        p.method == .get && isEmptyBody p.bodyAction),
    ("303 PUT → GET", expectPlan (decideRedirect origin (mkReq .put) false .seeOther (withLocation "/x")) fun p =>
        p.method == .get && isEmptyBody p.bodyAction),
    ("303 DELETE → GET", expectPlan (decideRedirect origin (mkReq .delete) false .seeOther (withLocation "/x")) fun p =>
        p.method == .get && isEmptyBody p.bodyAction),
    ("303 PATCH → GET", expectPlan (decideRedirect origin (mkReq .patch) false .seeOther (withLocation "/x")) fun p =>
        p.method == .get && isEmptyBody p.bodyAction),
    ("303 See Other preserves HEAD",
      expectPlan (decideRedirect origin (mkReq .head) false .seeOther (withLocation "/next")) fun p =>
        p.method == .head && isEmptyBody p.bodyAction),
    ("301 on POST downgrades to GET and drops the body",
      expectPlan (decideRedirect origin (mkReq .post) false .movedPermanently (withLocation "/x")) fun p =>
        p.method == .get && isEmptyBody p.bodyAction),
    ("302 on an HTTP/1.0 POST downgrades to GET and drops the body",
      expectPlan (decideRedirect origin (mkReq .post (version := .v10)) true .found
        (withLocation "http://other.example/login")) fun p =>
        p.method == .get && isEmptyBody p.bodyAction && p.isCrossOrigin),
    ("307 preserves POST and replays the body when replayable",
      expectPlan (decideRedirect origin (mkReq .post) true .temporaryRedirect (withLocation "/x")) fun p =>
        p.method == .post && isReplayBody p.bodyAction),
    ("308 keeps PUT and replays a replayable body",
      expectPlan (decideRedirect origin (mkReq .put) true .permanentRedirect (withLocation "/x")) fun p =>
        p.method == .put && isReplayBody p.bodyAction),
    ("301 on PUT keeps the method and replays a replayable body",
      expectPlan (decideRedirect origin (mkReq .put) true .movedPermanently (withLocation "/x")) fun p =>
        p.method == .put && isReplayBody p.bodyAction),
    ("302 on PATCH keeps the method and replays a replayable body",
      expectPlan (decideRedirect origin (mkReq .patch) true .found (withLocation "/x")) fun p =>
        p.method == .patch && isReplayBody p.bodyAction),
    ("302 on DELETE keeps the method and replays a replayable body",
      expectPlan (decideRedirect origin (mkReq .delete) true .found (withLocation "/x")) fun p =>
        p.method == .delete && isReplayBody p.bodyAction),
    ("307 on GET is followed with the method preserved",
      expectPlan (decideRedirect origin (mkReq .get) false .temporaryRedirect (withLocation "/x")) fun p =>
        p.method == .get)
  ] (·.2)

/-! ## Target (RFC 9112 §3.2, RFC 3986 §5.2.2) -/

#eval checkCases "Target rewriting" #[
    ("Cross-origin absolute `Location` keeps absolute-form on the wire",
      expectPlan (decideRedirect origin (mkReq .get credHeaders) false .found (withLocation "http://other.com/x"))
        fun p => p.isCrossOrigin && toString p.target == "http://other.com/x"),
    ("A protocol-relative redirect to the current origin is still same-origin",
      expectPlan (decideRedirect origin (mkReq .get) false .found (withLocation "//example.com/next")) fun p =>
        !p.isCrossOrigin && toString p.target == "/next")
  ] (·.2)

-- `/` parses to an absolute path with no segments, but it is not the empty reference, so it resolves
-- to `/` and drops the base query (RFC 3986 §5.2.2). The last case is the empty reference.
#eval checkCases "`/` versus the empty reference (#16036)" #[
    ("/ from /login?next=%2Fhome", "/login?next=%2Fhome", "/", "/"),
    ("/ drops the base query", "/a/b?old=1", "/", "/"),
    ("/?y", "/a/b?old=1", "/?y", "/?y"),
    ("/#f", "/a/b?old=1", "/#f", "/"),
    ("the empty reference", "/a/b?old=1", "", "/a/b?old=1")
  ] fun (label, from_, location, want) => expectEq label (targetFor from_ location) want

-- The bare path and the same-origin protocol-relative reference (first and fourth) are controls:
-- those branches already removed them.
#eval checkCases "Dot segments are removed whatever form the `Location` takes" #[
    ("bare path", "/a/../../etc/passwd", "/etc/passwd"),
    ("same-origin absolute", "http://example.com/a/../../etc/passwd", "/etc/passwd"),
    ("cross-origin absolute", "http://other.example/x/../../y", "http://other.example/y"),
    ("same-origin protocol-relative", "//example.com/x/../y", "/y"),
    ("cross-origin protocol-relative", "//other.example/x/./../y", "http://other.example/y")
  ] fun (label, location, want) => expectEq label (targetFor "/start" location) want

/-! ## Header scrubbing (RFC 9110 §15.4, §7.6.1) -/

private def sameOriginHopHeaders : Headers :=
  Headers.empty.insert .transferEncoding (Header.Value.ofString! "chunked")

private def xHop : Header.Name := Header.Name.ofString! "x-hop"

private def connectionNominatedHeaders : Headers :=
  Headers.empty
    |>.insert .connection (Header.Value.ofString! "x-hop")
    |>.insert xHop (Header.Value.ofString! "secret")

#eval checkCases "Header scrubbing" #[
    ("Cross-origin hop strips credential headers and rewrites Host to the new origin",
      expectPlan (decideRedirect origin (mkReq .get credHeaders) false .found (withLocation "http://other.com/x"))
        fun p => !p.headers.contains .authorization && !p.headers.contains .cookie &&
          (p.headers.get? .host).map (·.value) == some "other.com"),
    ("Same-origin hop keeps credential headers",
      expectPlan (decideRedirect origin (mkReq .get credHeaders) false .found (withLocation "/next")) fun p =>
        p.headers.contains .authorization && p.headers.contains .cookie && !p.isCrossOrigin),
    ("Changing the method to GET strips resource-specific content headers",
      expectPlan (decideRedirect origin (mkReq .post contentHeaders) false .seeOther (withLocation "/next"))
        fun p => p.method == .get && !p.headers.contains .contentType && !p.headers.contains .contentLength),
    ("A cross-origin hop on a request that carried no `Host` header leaves the plan without one",
      expectPlan (decideRedirect origin (mkReq .get) false .found (withLocation "http://other.com/x")) fun p =>
        p.isCrossOrigin && !p.headers.contains .host),
    ("Hop-by-hop headers are stripped even on same-origin redirects",
      expectPlan (decideRedirect origin (mkReq .post sameOriginHopHeaders) false .seeOther (withLocation "/next"))
        fun p => p.method == Method.get && !p.headers.contains .transferEncoding),
    ("`Connection` and the fields it nominates are removed",
      expectPlan (decideRedirect origin (mkReq .get connectionNominatedHeaders) false .found (withLocation "/next"))
        fun p => !p.headers.contains .connection && !p.headers.contains xHop)
  ] (·.2)
