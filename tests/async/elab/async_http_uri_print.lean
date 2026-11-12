module

import Std.Http.Test.Helpers
import Std.Http.Data.URI.Encoding

/-!
# URI printing

How URIs, request-targets and references print: round trips, the forms put on the wire, path
operations, updates and normalization, the builder, and printing that never turns a path into an
authority. RFC 3986 §3.3, §4.2, §5.2.4, §6.2.2; RFC 9112 §3.2; RFC 9110 §4.2.4; RFC 8089.
Regressions: #15246.
-/

open Std Http
open Std.Http.URI
open Std.Http.URI.Parser
open Std.Http.Internal.Test

private def target? (s : String) : Option RequestTarget :=
  ((parseRequestTarget <* Std.Internal.Parsec.eof).run s.toUTF8).toOption

/-- Fails unless `s` parses as a request-target that prints as `exact`. -/
private def expectPrints (s : String) (exact : String := s) : IO Unit :=
  match target? s with
  | some t => expectEq s (toString t) exact
  | none => throw <| IO.userError s!"{s.quote} did not parse"

private def relRef? (s : String) : Option URI.RelativeRef :=
  match URIReference.parse? s with
  | some (.relative r) => some r
  | _ => none

private def mkPath (segments : List String) (absolute : Bool) : URI.Path :=
  { segments := (segments.map URI.EncodedSegment.encode).toArray, absolute }

/-! ## Round trips (RFC 9112 §3.2) -/

#eval checkCases "Request Target Parsing - Basic Tests" #[
    ("///path/with/encoded%20space", "///path/with/encoded%20space", none),
    ("/path/with/encoded%20space", "/path/with/encoded%20space", none),
    ("/path/with/encoded%20space/", "/path/with/encoded%20space/", none),
    ("*", "*", none),
    ("/api/search?q=hello%20world&category=tech%2Bgames", "/api/search?q=hello%20world&category=tech%2Bgames", none),
    ("/", "/", none),
    ("/api/v1/users/123/posts/456/comments/789", "/api/v1/users/123/posts/456/comments/789", none),
    ("/files/../etc/passwd: dot segments kept", "/files/../etc/passwd", none),
    ("example.com:8080", "example.com:8080", none),
    ("https://example.com:8080/ata", "https://example.com:8080/ata", none),
    ("https://example.com:8080////./ata", "https://example.com:8080////./ata", none),
    ("192.168.1.1:3000", "192.168.1.1:3000", none),
    ("[::1]:8080", "[::1]:8080", none),
    ("http://example.com/path/to/resource?query=value", "http://example.com/path/to/resource?query=value", none),
    ("https://api.example.com:443/v1/users?limit=10", "https://api.example.com:443/v1/users?limit=10", none),
    ("http://[2001:db8::1]:8080/path", "http://[2001:db8::1]:8080/path", none),
    ("https://xn--nxasmq6b.xn--o3cw4h/path", "https://xn--nxasmq6b.xn--o3cw4h/path", none),
    ("http://exa_mple.com/path", "http://exa_mple.com/path", none),
    ("localhost:65535", "localhost:65535", none),
    ("http:80", "http:80", none),
    ("A request-target is printed without userinfo (RFC 9110 §4.2.4)",
      "https://user:pass@secure.example.com/private", some "https://secure.example.com/private"),
    ("/double//slash//path", "/double//slash//path", none),
    ("http://user%40example:pass%3Aword@host.com", "http://user%40example:pass%3Aword@host.com",
      some "http://host.com"),
    ("http://[::ffff:192.168.1.1]/path", "http://[::ffff:192.168.1.1]/path", none),
    ("http://example.com:/", "http://example.com:/", none),
    ("http://example.com:/?q=1", "http://example.com:/?q=1", none),
    ("///////", "///////", none)
  ] fun (_, s, exact) => expectPrints s (exact.getD s)


#eval checkCases "An empty path before a query or fragment (RFC 3986 §3.3)" #[
    "http://example.com?q=/foo", "http://example.com#abc"
  ] fun s => do
    let some u := URI.parse? s | throw <| IO.userError s!"{s} did not parse"
    ensure u.path.isEmpty s!"{s}: path {toString u.path}"
    expectEq "printed" (toString u) s


-- RFC 3986 §5.3: an empty authority is still an authority, so its `//` is printed.
#eval checkCases "An empty authority round-trips" #[
    "file:///tmp/junk.txt", "itms-services://?action=download-manifest", "x://y", "x:/y", "x:/"
  ] fun s => match URI.parse? s with
    | some u => expectEq s (toString u) s
    | none => throw <| IO.userError s!"{s.quote} did not parse"

/-! ## Wire forms (RFC 9112 §3.2.1–§3.2.3) -/

#eval checkCases "Request targets on the wire" #[
    ("RFC 9112 §3.2.1: an origin-form target is never empty",
      expectEq "originTarget" (toString (URI.parse! "http://example.com").originTarget) "/"),
    ("origin-form keeps the query",
      expectEq "originTarget" (toString (URI.parse! "http://example.com?q=1").originTarget) "/?q=1"),
    ("After an authority a non-empty path begins with `/`, or it would extend the host", do
      let u := (URI.parse! "http://example.com").withPath (mkPath ["evil"] false)
      ensure (toString u == "http://example.com/evil" && (URI.parse? (toString u)).bind (·.host?) == u.host?)
        s!"printed {toString u}"),
    ("in origin-form a non-empty path begins with `/`",
      expectEq "originForm" (toString (RequestTarget.originForm (mkPath ["x"] false) none)) "/x"),
    ("absolute-form printed without userinfo or fragment", do
      let absolute := RequestTarget.absoluteForm (URI.parse! "http://user:secret@example.com/x?q#frag")
      expectEq "absolute-form" (toString absolute) "http://example.com/x?q"),
    ("authority-form printed without userinfo", do
      let some authority := (URI.parse! "http://u:p@example.com:443/").authority
        | throw (IO.userError "no authority")
      expectEq "authority-form" (toString (RequestTarget.authorityForm authority)) "example.com:443")
  ] (·.2)


#eval checkCases "Origin-form from components (RFC 9112 §3.2.1)" #[
    ("a `?` in a segment", expectEq "printed" (toString (RequestTarget.originForm (mkPath ["a?b"] true) none)) "/a%3Fb"),
    ("a space in a segment", expectEq "printed" (toString (RequestTarget.originForm (mkPath ["a b"] true) none)) "/a%20b"),
    ("a path that starts with `//` reads back as the same path", do
      let t := RequestTarget.originForm (mkPath ["", "evil.com", "x"] true) none
      match RequestTarget.parse? (toString t) with
      | some (.originForm path _) => expectEq "segments" (path.segments.map toString) #["", "evil.com", "x"]
      | other => throw <| IO.userError s!"{toString t} read back as {reprLine other}")
  ] (·.2)

/-! ## Path operations (RFC 3986 §5.2.4) -/

#eval checkCases "Path.normalize Tests (RFC 3986 Section 5.2.4)" #[
    ("/a/./b", "http://example.com/a/./b", "/a/b"),
    ("a trailing `/..` leaves a `/` (step 2B)", "http://example.com/a/b/..", "/a/"),
    ("/a/b/c/./../../g", "http://example.com/a/b/c/./../../g", "/a/g"),
    ("/../../../g", "http://example.com/../../../g", "/g"),
    ("/a/b/../c", "http://example.com/a/b/../c", "/a/c"),
    ("/a/b/c/../.././", "http://example.com/a/b/c/../.././", "/a/"),
    ("/a/b/../../..", "http://example.com/a/b/../../..", "/"),
    ("/../../../", "http://example.com/../../../", "/"),
    ("Likewise for a trailing `/.` (step 2C)", "http://example.com/./a/./b/./c/.", "/a/b/c/"),
    ("/a/../b/../c", "http://example.com/a/../b/../c", "/c")
  ] fun (label, s, want) => expectEq label (toString (URI.parse! s).path.normalize) want

#eval checkCases "Path.parent Tests" #[
    ("/a/b/c", "http://example.com/a/b/c", "/a/b"),
    ("/a/b", "http://example.com/a/b", "/a"),
    ("/a", "http://example.com/a", "/"),
    ("/", "http://example.com/", "/")
  ] fun (label, s, want) => expectEq label (toString (URI.parse! s).path.parent) want

#eval checkCases "Path.join Tests" #[
    ("relative", false, "/a/b/c/d"),
    ("absolute replaces", true, "/x/y")
  ] fun (label, absolute, want) => do
    let p1 := (URI.parse! "http://example.com/a/b").path
    let segs := if absolute then #["x", "y"] else #["c", "d"]
    let p2 : URI.Path := { segments := segs.map URI.EncodedString.encode, absolute }
    expectEq label (toString (p1.join p2)) want

#eval checkCases "Path.isEmpty Tests" #[
    ("http://example.com: isEmpty", ensure (URI.parse! "http://example.com").path.isEmpty "isEmpty"),
    ("http://example.com/: absolute", ensure (URI.parse! "http://example.com/").path.absolute "absolute"),
    ("http://example.com/a: not isEmpty", ensure (!(URI.parse! "http://example.com/a").path.isEmpty) "isEmpty"),
    ("http://example.com/a: absolute", ensure (URI.parse! "http://example.com/a").path.absolute "absolute")
  ] (·.2)


#eval checkCases "Segments that only look like dot segments are kept (RFC 3986 §5.2.4)" #[
    ("/%2e.bar", "/%2e.bar", "/%2e.bar"),
    ("/foo/..bar", "/foo/..bar", "/foo/..bar"),
    ("/.foo", "/.foo", "/.foo"),
    ("/...", "/...", "/..."),
    ("%2E%2E is not ..", "/a/%2E%2E/b", "/a/%2E%2E/b")
  ] fun (label, path, want) =>
    expectEq label (toString (URI.parse! s!"http://example.com{path}").path.normalize) want

/-! ## Updates and normalization (RFC 3986 §6.2.2) -/

#eval checkCases "URI Modification Helpers" #[
    ("withScheme! htTps", expectEq "scheme" ((URI.parse! "http://example.com").withScheme! "htTps" |>.scheme).val
      "https"),
    ("withScheme! ftP", expectEq "scheme" ((URI.parse! "http://example.com").withScheme! "ftP" |>.scheme).val "ftp"),
    ("withFragment", expectEq "withFragment"
      (toString ((URI.parse! "http://example.com/").withFragment
        (some (toString (URI.EncodedString.encode "section1" : URI.EncodedFragment)))))
      "http://example.com/#section1"),
    ("withQuery", expectEq "withQuery"
      (toString ((URI.parse! "http://example.com/").withQuery (URI.Query.empty.insert "key" "value")))
      "http://example.com/?key=value"),
    ("withPath", do
      let newPath : URI.Path :=
        { segments := #[URI.EncodedString.encode "new", URI.EncodedString.encode "path"], absolute := true }
      expectEq "withPath" (toString ((URI.parse! "http://example.com/old/path").withPath newPath))
        "http://example.com/new/path")
  ] (·.2)

#eval checkCases "URI.normalize Tests (RFC 3986 Section 6)" #[
    ("scheme HTTP", expectEq "scheme" (URI.parse! "HTTP://example.com").normalize.scheme.val "http"),
    ("scheme HtTpS", expectEq "scheme" (URI.parse! "HtTpS://example.com").normalize.scheme.val "https"),
    ("host EXAMPLE.COM", expectEq "normalize" (toString (URI.parse! "http://EXAMPLE.COM/").normalize)
      "http://example.com/"),
    ("host Example.COM", expectEq "normalize" (toString (URI.parse! "HTTP://Example.COM/").normalize)
      "http://example.com/"),
    ("dot segments", expectEq "normalize" (toString (URI.parse! "http://example.com/a/b/../c").normalize)
      "http://example.com/a/c"),
    ("dot segments and case", expectEq "normalize"
      (toString (URI.parse! "HTTP://EXAMPLE.COM/a/b/c/./../../g").normalize) "http://example.com/a/g"),
    ("path case is kept", expectEq "normalize" (toString (URI.parse! "HTTPS://WWW.EXAMPLE.COM/PATH").normalize)
      "https://www.example.com/PATH")
  ] (·.2)

/-! ## Builder -/

#eval checkCases "URI Builder Tests" #[
    ("path and query", expectEq "build" (toString (URI.Builder.empty
      |>.setScheme! "https"
      |>.setHost! "example.com"
      |>.appendPathSegment "api"
      |>.appendPathSegment "users"
      |>.addQueryParam "page" "1"
      |>.build)) "https://example.com/api/users?page=1"),
    ("port and no path", expectEq "build" (toString (URI.Builder.empty
      |>.setScheme! "http"
      |>.setHost! "localhost"
      |>.setPort 8080
      |>.build)) "http://localhost:8080/"),
    ("userinfo", expectEq "build" (toString (URI.Builder.empty
      |>.setScheme! "https"
      |>.setUserInfo "user" (some "pass")
      |>.setHost! "secure.example.com"
      |>.appendPathSegment "private"
      |>.build)) "https://user:pass@secure.example.com/private"),
    ("A `:` in a username: printed", do
      let uri := URI.Builder.empty |>.setScheme! "http" |>.setHost! "example.com"
        |>.setUserInfo "a:b" (some "pw") |>.build
      expectEq "printed" (toString uri) "http://a%3Ab:pw@example.com/"),
    ("A `:` in a username: read back", do
      let uri := URI.Builder.empty |>.setScheme! "http" |>.setHost! "example.com"
        |>.setUserInfo "a:b" (some "pw") |>.build
      let userInfo := (URI.parse! (toString uri)).authority.bind (·.userInfo)
      ensure (userInfo.bind (·.username?) == some "a:b" && userInfo.bind (·.password?) == some "pw")
        s!"read back as username {userInfo.bind (·.username?)}, password {userInfo.bind (·.password?)}"),
    ("literal pluses, and https by default (#15246)", do
      let uri := Builder.empty
        |>.setHost! "example.com"
        |>.appendPathSegment "a+b"
        |>.addQueryParam "a+b" "x+y"
        |>.addQueryParam "a b" "x y"
        |>.addQueryFlag "+"
        |>.build
      ensure (toString uri == "https://example.com/a+b?a%2Bb=x%2By&a+b=x+y&%2B" &&
        (uri.query.bind (·.get "a+b")) == some "x+y" && (uri.query.bind (·.get "+")) == some "")
        s!"built {toString uri}")
  ] (·.2)

/-! ## Authority-safe printing (RFC 3986 §3.3, §4.2) -/

-- Without an authority a path cannot begin with `//` (RFC 3986 §3.3), so such a path is printed
-- behind a `/.` segment instead of as `//host`, which names a host.
#eval checkCases "A path that begins with `//` never prints as an authority" #[
    ("`http:////evil.com/x` has an empty authority and so names no host", ensure (match URI.parse? "http:////evil.com/x" with
      | some u => u.host?.isNone && toString u == "http:/.//evil.com/x" &&
          (URI.parse? (toString u)).any (·.host?.isNone)
      | none => false) "http:////evil.com/x"),
    ("Removing dot segments can leave a path that begins with `//` and no authority", do
      let u := (URI.parse! "http:/.//evil.com/x").normalize
      ensure (toString u == "http:/.//evil.com/x" && (URI.parse? (toString u)).any (·.host?.isNone))
        s!"printed {toString u}"),
    ("so can a builder with no host", do
      let u := URI.Builder.empty |>.setScheme! "http" |>.setPath #["", "evil.com"] |>.build
      ensure ((URI.parse? (toString u)).any (·.host?.isNone)) s!"printed {toString u}"),
    ("An empty authority before such a path (`file:////host/share`, RFC 8089 Appendix E.3.2) parses",
      ensure (match URI.parse? "file:////host/share" with
      | some u => u.host?.isNone && toString u == "file:/.//host/share" &&
          (URI.parse? (toString u)).map (·.path.normalize) == some u.path
      | none => false) "file:////host/share"),
    ("The same holds for a reference, where `//` would read as an authority", ensure (match relRef? "/.//evil.com/x" with
      | some r =>
        let r := { r with path := r.path.normalize }
        toString r == "/.//evil.com/x" && (relRef? (toString r)).any (·.authority.isNone)
      | none => false) "/.//evil.com/x"),
    ("RFC 3986 §4.2: a first segment with `:` is printed behind a `./` segment", ensure (match relRef? "./a:b" with
      | some r =>
        let r := { r with path := r.path.normalize }
        toString r == "./a:b" && (relRef? (toString r)).isSome
      | none => false) "./a:b"),
    ("A relative path that begins with an empty segment would print as an absolute path", do
      let r : URI.RelativeRef := { authority := none, path := mkPath ["", "x"] false, fragment := none }
      ensure (toString r == ".//x" && (relRef? (toString r)).any (·.path.normalize == r.path))
        s!"printed {toString r}")
  ] (·.2)
