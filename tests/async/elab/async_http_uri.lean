/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
import Std.Http.Data.URI
import Std.Http.Data.URI.Encoding

open Std.Http
open Std.Http.URI
open Std.Http.URI.Parser

/-!
# URI Tests

Comprehensive tests for URI parsing, encoding, normalization, and manipulation.
This file consolidates tests from multiple URI-related test files.
-/

-- ============================================================================
-- Helper Functions
-- ============================================================================

def runParser (parser : Std.Internal.Parsec.ByteArray.Parser α) (s : String) : IO α :=
  IO.ofExcept ((parser <* Std.Internal.Parsec.eof).run s.toUTF8)

def parseCheck (s : String) (exact : String := s) : IO Unit := do
  let result ← runParser parseRequestTarget s
  if toString result = exact then
    pure ()
  else
    throw (.userError s!"expect {exact.quote} but got {(toString result).quote}")

def parseCheckFail (s : String) : IO Unit := do
  match (parseRequestTarget <* Std.Internal.Parsec.eof).run s.toUTF8 with
  | .ok r =>
      throw <| .userError
        s!"expected parse failure, but succeeded with {(repr r)}"
  | .error _ =>
      pure ()

-- ============================================================================
-- Percent Encoding Tests (EncodedString)
-- ============================================================================

-- Valid percent encoding validation
/--
info: some "abc"
-/
#guard_msgs in
#eval IO.println (repr (EncodedSegment.ofByteArray? "abc".toUTF8))

/--
info: some "%20"
-/
#guard_msgs in
#eval IO.println (repr (EncodedSegment.ofByteArray? "%20".toUTF8))

/--
info: some "hello%20world"
-/
#guard_msgs in
#eval IO.println (repr (EncodedSegment.ofByteArray? "hello%20world".toUTF8))

/--
info: some "%FF"
-/
#guard_msgs in
#eval IO.println (repr (EncodedSegment.ofByteArray? "%FF".toUTF8))

/--
info: some "%00"
-/
#guard_msgs in
#eval IO.println (repr (EncodedSegment.ofByteArray? "%00".toUTF8))

-- Invalid percent encoding: incomplete
/--
info: none
-/
#guard_msgs in
#eval IO.println (repr (EncodedSegment.ofByteArray? "%".toUTF8))

/--
info: none
-/
#guard_msgs in
#eval IO.println (repr (EncodedSegment.ofByteArray? "hello%".toUTF8))

/--
info: none
-/
#guard_msgs in
#eval IO.println (repr (EncodedSegment.ofByteArray? "%2".toUTF8))

/--
info: none
-/
#guard_msgs in
#eval IO.println (repr (EncodedSegment.ofByteArray? "%A".toUTF8))

-- Invalid percent encoding: non-hex characters
/--
info: none
-/
#guard_msgs in
#eval IO.println (repr (EncodedSegment.ofByteArray? "%GG".toUTF8))

/--
info: none
-/
#guard_msgs in
#eval IO.println (repr (EncodedSegment.ofByteArray? "%2G".toUTF8))

/--
info: none
-/
#guard_msgs in
#eval IO.println (repr (EncodedSegment.ofByteArray? "%G2".toUTF8))

-- ============================================================================
-- Percent Encoding Decode Tests
-- ============================================================================

/--
info: some "abc"
-/
#guard_msgs in
#eval IO.println (repr <| EncodedSegment.decode =<< (EncodedSegment.ofByteArray? "abc".toUTF8))

/--
info: some " "
-/
#guard_msgs in
#eval IO.println (repr <| EncodedSegment.decode =<< (EncodedSegment.ofByteArray? "%20".toUTF8))

/--
info: some "hello world"
-/
#guard_msgs in
#eval IO.println (repr <| EncodedSegment.decode =<< (EncodedSegment.ofByteArray? "hello%20world".toUTF8))

/--
info: some " !"
-/
#guard_msgs in
#eval IO.println (repr <| EncodedSegment.decode =<< (EncodedSegment.ofByteArray? "%20%21".toUTF8))

/--
info: none
-/
#guard_msgs in
#eval IO.println (repr <| EncodedSegment.decode =<< (EncodedSegment.ofByteArray? "%FF".toUTF8))

/--
info: some "\x00"
-/
#guard_msgs in
#eval IO.println (repr <| EncodedSegment.decode =<< (EncodedSegment.ofByteArray? "%00".toUTF8))

-- ============================================================================
-- Query String Encoding Tests
-- ============================================================================

/--
info: some "hello+world"
-/
#guard_msgs in
#eval IO.println (repr (EncodedQueryString.ofByteArray? "hello+world".toUTF8))

/--
info: none
-/
#guard_msgs in
#eval IO.println (repr (EncodedQueryString.ofByteArray? "%".toUTF8))

/--
info: some "hello world"
-/
#guard_msgs in
#eval IO.println (repr <| EncodedQueryString.decode =<< (EncodedQueryString.ofByteArray? "hello+world".toUTF8))

/--
info: some " "
-/
#guard_msgs in
#eval IO.println (repr <| EncodedQueryString.decode =<< (EncodedQueryString.ofByteArray? "%20".toUTF8))

-- ============================================================================
-- Request Target Parsing - Basic Tests
-- ============================================================================

#eval parseCheck "///path/with/encoded%20space"
#eval parseCheck "/path/with/encoded%20space"
#eval parseCheck "/path/with/encoded%20space/"
#eval parseCheck "*"
#eval parseCheck "/api/search?q=hello%20world&category=tech%2Bgames"
#eval parseCheck "/"
#eval parseCheck "/api/v1/users/123/posts/456/comments/789"
#eval parseCheck "/files/../etc/passwd"
#eval parseCheck "example.com:8080"
#eval parseCheck "https://example.com:8080/ata"
#eval parseCheck "https://example.com:8080////./ata"
#eval parseCheck "192.168.1.1:3000"
#eval parseCheck "[::1]:8080"
#eval parseCheck "http://example.com/path/to/resource?query=value"
#eval parseCheck "https://api.example.com:443/v1/users?limit=10"
#eval parseCheck "http://[2001:db8::1]:8080/path"
#eval parseCheck "https://xn--nxasmq6b.xn--o3cw4h/path"
#eval parseCheck "http://exa_mple.com/path"
#eval parseCheck "localhost:65535"
#eval parseCheck "http:80"
-- A request-target is printed without userinfo (RFC 9110 §4.2.4).
#eval parseCheck "https://user:pass@secure.example.com/private" "https://secure.example.com/private"
#eval parseCheck "/double//slash//path"
#eval parseCheck "http://user%40example:pass%3Aword@host.com" "http://host.com"
#eval parseCheck "http://[::ffff:192.168.1.1]/path"
#eval parseCheck "http://example.com:/"
#eval parseCheck "http://example.com:/?q=1"
#eval parseCheck "///////"

-- `&` in a key must be percent-encoded so toRawString round-trips correctly.
#guard
  let query := URI.Query.empty.insert "a&b" "1"
  query.toRawString == "a%26b=1"

-- `=` in a key must be percent-encoded so re-parsing preserves the key.
#guard
  let query := URI.Query.empty.insert "a=b" "1"
  query.toRawString == "a%3Db=1"

-- `&` in a value must be percent-encoded.
#guard
  let query := URI.Query.empty.insert "key" "a&b"
  query.toRawString == "key=a%26b"

-- `=` in a value is technically safe (parser uses first `=`), but encoding it
-- is still correct and keeps representation unambiguous.
#guard
  let query := URI.Query.empty.insert "key" "a=b"
  query.toRawString == "key=a%3Db"

-- Round-trip: insert → toRawString → re-parse should preserve the parameter.
#guard
  let original := URI.Query.empty.insert "a&b" "c=d"
  let raw := original.toRawString
  -- Parse via a synthetic origin-form request target
  match (URI.Parser.parseRequestTarget <* Std.Internal.Parsec.eof).run
      s!"/path?{raw}".toUTF8 with
  | .ok result =>
      (result.query.get "a&b" == some "c=d")
  | .error _ => false

#guard
  match (parseRequestTarget <* Std.Internal.Parsec.eof).run "http:80".toUTF8 with
  | .ok (.authorityForm _) => true
  | _ => false

-- Parse failure tests
#eval parseCheckFail "/path with space"
#eval parseCheckFail "/path/%"
#eval parseCheckFail "/path/%2"
#eval parseCheckFail "/path/%ZZ"
#eval parseCheckFail ""
#eval parseCheckFail "[::1"
#eval parseCheckFail "[:::1]:80"
#eval parseCheckFail "http://-example.com/path"
#eval parseCheckFail "http://[fe80::1%25eth0]/path"
#eval parseCheckFail "#frag"
#eval parseCheckFail "/path/\n"
#eval parseCheckFail "/path/\u0000"
#eval parseCheckFail "/page#section"
#eval parseCheckFail "/api/v1/users/[id]:action"

-- maxPathSegments should apply to trailing empty segments as well.
#guard
  match (parseURI { maxPathSegments := 1 } <* Std.Internal.Parsec.eof).run
      "http://example.com/a/".toUTF8 with
  | .error _ => true
  | .ok _ => false

-- ============================================================================
-- Request Target Parsing - Detailed Output Tests
-- ============================================================================

/--
info: Std.Http.RequestTarget.originForm { segments := #["path", "with", "encoded%20space"], absolute := true } none
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "/path/with/encoded%20space"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.originForm { segments := #["", "", "path", "with", "encoded%20space"], absolute := true } none
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "///path/with/encoded%20space"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.asteriskForm
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "*"
  IO.println (repr result)

/--
info: #[("q", some "hello%20world"), ("category", some "tech%2Bgames")]
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "/api/search?q=hello%20world&category=tech%2Bgames"
  IO.println (repr result.query)

/--
info: Std.Http.RequestTarget.originForm { segments := #[], absolute := true } none
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "/"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.authorityForm
  { userInfo := none, host := Std.Http.URI.Host.name "example.com", port := Std.Http.URI.Port.value 8080 }
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "example.com:8080"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.authorityForm
  { userInfo := none, host := Std.Http.URI.Host.ipv4 192.168.1.1, port := Std.Http.URI.Port.value 3000 }
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "192.168.1.1:3000"
  IO.println (repr result)

-- A host that begins with an IPv4 address and goes on is a name.
/--
info: Std.Http.RequestTarget.authorityForm
  { userInfo := none, host := Std.Http.URI.Host.name "1.2.3.4-x.example", port := Std.Http.URI.Port.value 443 }
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "1.2.3.4-x.example:443"
  IO.println (repr result)

#guard
  match (parseRequestTarget <* Std.Internal.Parsec.eof).run "http://1.2.3.4x.example/".toUTF8 with
  | .ok (.absoluteForm uri) => uri.authority.any fun a => toString a.host == "1.2.3.4x.example"
  | _ => false

#guard
  match (parseHostHeader <* Std.Internal.Parsec.eof).run "1.2.3.4-x.example:8080".toUTF8 with
  | .ok (host, port) => toString host == "1.2.3.4-x.example" && port == .value 8080
  | .error _ => false

#guard
  match (parseHostHeader <* Std.Internal.Parsec.eof).run "1.2.3.4".toUTF8 with
  | .ok (.ipv4 _, .omitted) => true
  | _ => false

/--
info: Std.Http.RequestTarget.authorityForm
  { userInfo := none, host := Std.Http.URI.Host.ipv6 ::1, port := Std.Http.URI.Port.value 8080 }
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "[::1]:8080"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.absoluteForm
  { scheme := "https",
    authority := some { userInfo := none,
                   host := Std.Http.URI.Host.name "example.com",
                   port := Std.Http.URI.Port.value 8080 },
    path := { segments := #["ata"], absolute := true },
    query := none,
    fragment := none }
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "https://example.com:8080/ata"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.absoluteForm
  { scheme := "http",
    authority := some { userInfo := none,
                   host := Std.Http.URI.Host.ipv6 2001:db8::1,
                   port := Std.Http.URI.Port.value 8080 },
    path := { segments := #["path"], absolute := true },
    query := none,
    fragment := none }
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "http://[2001:db8::1]:8080/path"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.absoluteForm
  { scheme := "https",
    authority := some { userInfo := some { username := "user%20b", password := some "pass" },
                   host := Std.Http.URI.Host.name "secure.example.com",
                   port := Std.Http.URI.Port.omitted },
    path := { segments := #["private"], absolute := true },
    query := none,
    fragment := none }
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "https://user%20b:pass@secure.example.com/private"
  IO.println (repr result)

-- ============================================================================
-- IPv6 Host Tests
-- ============================================================================

/--
info: Std.Http.URI.Host.ipv6 ::1
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "[::1]:8080"
  match result.authority? with
  | some auth => IO.println (repr auth.host)
  | none => IO.println "no authority"

/--
info: Std.Http.URI.Host.ipv6 2001:db8::8a2e:370:7334
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "http://[2001:db8::8a2e:370:7334]:8080/api"
  match result.authority? with
  | some auth => IO.println (repr auth.host)
  | none => IO.println "no authority"

/--
info: Std.Http.URI.Host.ipv6 ::
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "http://[::]/path"
  match result.authority? with
  | some auth => IO.println (repr auth.host)
  | none => IO.println "no authority"

-- ============================================================================
-- UserInfo Tests
-- ============================================================================

/--
info: some { username := "user", password := some "pass" }
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "https://user:pass@example.com/private"
  match result.authority? with
  | some auth => IO.println (repr auth.userInfo)
  | none => IO.println "no authority"

/--
info: some { username := "user%20only", password := none }
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "https://user%20only@example.com/path"
  match result.authority? with
  | some auth => IO.println (repr auth.userInfo)
  | none => IO.println "no authority"

/--
info: some { username := "", password := some "pass" }
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "https://:pass@example.com/path"
  match result.authority? with
  | some auth => IO.println (repr auth.userInfo)
  | none => IO.println "no authority"

/--
info: some { username := "user", password := some "p%40ss%3Aw0rd" }
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "https://user:p%40ss%3Aw0rd@example.com/"
  match result.authority? with
  | some auth => IO.println (repr auth.userInfo)
  | none => IO.println "no authority"

-- ============================================================================
-- Path.normalize Tests (RFC 3986 Section 5.2.4)
-- ============================================================================

/--
info: /a/b
-/
#guard_msgs in
#eval IO.println <| toString (URI.parse! "http://example.com/a/./b").path.normalize

-- RFC 3986 §5.2.4 step 2B replaces a trailing `/..` with `/`, so the result still names a
-- collection.
/--
info: /a/
-/
#guard_msgs in
#eval IO.println (URI.parse! "http://example.com/a/b/..").path.normalize

/--
info: /a/g
-/
#guard_msgs in
#eval IO.println (URI.parse! "http://example.com/a/b/c/./../../g").path.normalize

/--
info: /g
-/
#guard_msgs in
#eval IO.println (URI.parse! "http://example.com/../../../g").path.normalize

/--
info: /a/c
-/
#guard_msgs in
#eval IO.println (URI.parse! "http://example.com/a/b/../c").path.normalize

/--
info: /a/
-/
#guard_msgs in
#eval IO.println (URI.parse! "http://example.com/a/b/c/../.././").path.normalize

/--
info: /
-/
#guard_msgs in
#eval IO.println (URI.parse! "http://example.com/a/b/../../..").path.normalize

/--
info: /
-/
#guard_msgs in
#eval IO.println (URI.parse! "http://example.com/../../../").path.normalize

-- Likewise for a trailing `/.` (RFC 3986 §5.2.4 step 2C).
/--
info: /a/b/c/
-/
#guard_msgs in
#eval IO.println (URI.parse! "http://example.com/./a/./b/./c/.").path.normalize

/--
info: /c
-/
#guard_msgs in
#eval IO.println (URI.parse! "http://example.com/a/../b/../c").path.normalize

-- ============================================================================
-- Path.parent Tests
-- ============================================================================

/--
info: /a/b
-/
#guard_msgs in
#eval IO.println (URI.parse! "http://example.com/a/b/c").path.parent

/--
info: /a
-/
#guard_msgs in
#eval IO.println (URI.parse! "http://example.com/a/b").path.parent

/--
info: /
-/
#guard_msgs in
#eval IO.println (URI.parse! "http://example.com/a").path.parent

/--
info: /
-/
#guard_msgs in
#eval IO.println (URI.parse! "http://example.com/").path.parent

-- ============================================================================
-- Path.join Tests
-- ============================================================================

/--
info: /a/b/c/d
-/
#guard_msgs in
#eval do
  let p1 := (URI.parse! "http://example.com/a/b").path
  let p2 : URI.Path := { segments := #[URI.EncodedString.encode "c", URI.EncodedString.encode "d"], absolute := false }
  IO.println (p1.join p2)

/--
info: /x/y
-/
#guard_msgs in
#eval do
  let p1 := (URI.parse! "http://example.com/a/b").path
  let p2 : URI.Path := { segments := #[URI.EncodedString.encode "x", URI.EncodedString.encode "y"], absolute := true }
  IO.println (p1.join p2)

-- ============================================================================
-- Path.isEmpty Tests
-- ============================================================================

#guard (URI.parse! "http://example.com").path.isEmpty = true
#guard (URI.parse! "http://example.com/").path.absolute = true
#guard (URI.parse! "http://example.com/a").path.isEmpty = false
#guard (URI.parse! "http://example.com/a").path.absolute = true

-- ============================================================================
-- URI Modification Helpers
-- ============================================================================

#guard ((URI.parse! "http://example.com").withScheme! "htTps" |>.scheme) == "https"
#guard ((URI.parse! "http://example.com").withScheme! "ftP" |>.scheme) == "ftp"

/--
info: http://example.com/#section1
-/
#guard_msgs in
#eval IO.println ((URI.parse! "http://example.com/").withFragment (some (toString (URI.EncodedString.encode "section1" : URI.EncodedFragment))))

/--
info: http://example.com/?key=value
-/
#guard_msgs in
#eval do
  let uri := URI.parse! "http://example.com/"
  let query := URI.Query.empty.insert "key" "value"
  IO.println (uri.withQuery query)

/--
info: http://example.com/new/path
-/
#guard_msgs in
#eval do
  let uri := URI.parse! "http://example.com/old/path"
  let newPath : URI.Path := { segments := #[URI.EncodedString.encode "new", URI.EncodedString.encode "path"], absolute := true }
  IO.println (uri.withPath newPath)

-- ============================================================================
-- URI.normalize Tests (RFC 3986 Section 6)
-- ============================================================================

#guard (URI.parse! "HTTP://example.com").normalize.scheme == "http"
#guard (URI.parse! "HtTpS://example.com").normalize.scheme == "https"

/--
info: http://example.com/
-/
#guard_msgs in
#eval IO.println (URI.parse! "http://EXAMPLE.COM/").normalize

/--
info: http://example.com/
-/
#guard_msgs in
#eval IO.println (URI.parse! "HTTP://Example.COM/").normalize

/--
info: http://example.com/a/c
-/
#guard_msgs in
#eval IO.println (URI.parse! "http://example.com/a/b/../c").normalize

/--
info: http://example.com/a/g
-/
#guard_msgs in
#eval IO.println (URI.parse! "HTTP://EXAMPLE.COM/a/b/c/./../../g").normalize

/--
info: https://www.example.com/PATH
-/
#guard_msgs in
#eval IO.println (URI.parse! "HTTPS://WWW.EXAMPLE.COM/PATH").normalize

-- ============================================================================
-- Query Parameter Tests
-- ============================================================================

-- Query with duplicate keys
/--
info: 3
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "/search?tag=a&tag=b&tag=c"
  let all := result.query.findAll "tag"
  IO.println all.size

/--
info: #[some "a", some "b", some "c"]
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "/search?tag=a&tag=b&tag=c"
  let all := result.query.findAll "tag"
  IO.println (repr all)

/--
info: some (some "a")
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "/search?key=a&key=b&key=c"
  IO.println (repr (result.query.find? "key"))

-- Empty value vs no value
/--
info: some (some "")
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "/api?key="
  IO.println (repr (result.query.find? "key"))

/--
info: some none
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "/api?key"
  IO.println (repr (result.query.find? "key"))

/--
info: some (some "value")
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "/api?key=value"
  IO.println (repr (result.query.find? "key"))

-- `String`-keyed lookups match every spelling of a name; `*Encoded` lookups match exact bytes.
#guard
  match (parseRequestTarget <* Std.Internal.Parsec.eof).run "/api?%61=1&a=2".toUTF8 with
  | .ok result =>
      let encodedA? := EncodedQueryParam.fromString? "%61"
      ((result.query.find? "a" |>.bind id |>.bind EncodedQueryParam.decode) == some "1") &&
      (result.query.findAll "a").size == 2 &&
      (result.query.find? "%61").isNone &&
      result.query.contains "a" &&
      !result.query.contains "%61" &&
      (match encodedA? with
       | some encodedA =>
           ((result.query.findEncoded? encodedA |>.bind id |>.bind EncodedQueryParam.decode) == some "1") &&
           result.query.containsEncoded encodedA
       | none => false)
  | .error _ => false

#guard
  match (parseRequestTarget <* Std.Internal.Parsec.eof).run "/api?%61=1&a=2".toUTF8 with
  | .ok result =>
      match EncodedQueryParam.fromString? "%61" with
      | some encodedA =>
          let erasedRaw := result.query.erase "a"
          let erasedEncoded := result.query.eraseEncoded encodedA
          !erasedRaw.contains "a" &&
          !erasedRaw.containsEncoded encodedA &&
          !erasedEncoded.containsEncoded encodedA &&
          erasedEncoded.contains "a"
      | none => false
  | .error _ => false

-- ============================================================================
-- Query Operations
-- ============================================================================

-- #14934: a name a browser percent-encodes is found by its decoded spelling.
def browserQuery : URI.Query :=
  match EncodedQueryParam.fromString? "a%3Ab", EncodedQueryParam.fromString? "on" with
  | some k, some v => URI.Query.empty.insertEncoded k (some v)
  | _, _ => URI.Query.empty

#guard browserQuery.get "a:b" == some "on"
#guard browserQuery.getD "a:b" "off" == "on"
#guard browserQuery.contains "a:b"
#guard (browserQuery.findAll "a:b").size == 1
#guard !browserQuery.contains "a%3Ab"
#guard (browserQuery.erase "a:b").isEmpty
#guard toString (browserQuery.set "a:b" "off") == "?a:b=off"
#guard
  match (parseRequestTarget <* Std.Internal.Parsec.eof).run "/consent?a%3Ab=on".toUTF8 with
  | .ok result => result.query.get "a:b" == some "on"
  | .error _ => false
#guard (URI.parse? "https://example.com/consent?a%3Ab=on").bind (·.query.bind (·.get "a:b")) == some "on"

#guard (URI.Query.empty.insert "a" "1" |>.contains "a") = true
#guard (URI.Query.empty.contains "nonexistent") = false

/--
info: a=1&b=2
-/
#guard_msgs in
#eval do
  let query := URI.Query.empty
    |>.insert "a" "1"
    |>.insert "b" "2"
  IO.println query.toRawString

/--
info: b=2
-/
#guard_msgs in
#eval do
  let query := URI.Query.empty
    |>.insert "a" "1"
    |>.insert "b" "2"
    |>.erase "a"
  IO.println query.toRawString

/--
info: key=new
-/
#guard_msgs in
#eval do
  let query := URI.Query.empty
    |>.insert "key" "old"
    |>.set "key" "new"
  IO.println query.toRawString

-- ============================================================================
-- URI Builder Tests
-- ============================================================================

-- Domain names longer than 255 characters are rejected.
#guard
  let label := String.ofList (List.replicate 63 'a')
  let longDomain := s!"{label}.{label}.{label}.{label}."
  (URI.DomainName.ofString? longDomain).isNone

#guard
  let label := String.ofList (List.replicate 63 'a')
  let longDomain := s!"{label}.{label}.{label}.{label}."
  (URI.Builder.empty.setHost? longDomain).isNone

/--
info: https://example.com/api/users?page=1
-/
#guard_msgs in
#eval do
  let uri := URI.Builder.empty
    |>.setScheme! "https"
    |>.setHost! "example.com"
    |>.appendPathSegment "api"
    |>.appendPathSegment "users"
    |>.addQueryParam "page" "1"
    |>.build
  IO.println uri

/--
info: http://localhost:8080/
-/
#guard_msgs in
#eval do
  let uri := URI.Builder.empty
    |>.setScheme! "http"
    |>.setHost! "localhost"
    |>.setPort 8080
    |>.build
  IO.println uri

/--
info: https://user:pass@secure.example.com/private
-/
#guard_msgs in
#eval do
  let uri := URI.Builder.empty
    |>.setScheme! "https"
    |>.setUserInfo "user" (some "pass")
    |>.setHost! "secure.example.com"
    |>.appendPathSegment "private"
    |>.build
  IO.println uri

-- ============================================================================
-- Encoded Path Segment Tests
-- ============================================================================

/--
info: Std.Http.RequestTarget.originForm { segments := #["path%2Fwith%2Fslashes"], absolute := true } none
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "/path%2Fwith%2Fslashes"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.originForm { segments := #["file%20name.txt"], absolute := true } none
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "/file%20name.txt"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.originForm { segments := #["caf%C3%A9"], absolute := true } none
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "/caf%C3%A9"
  IO.println (repr result)

-- ============================================================================
-- Authority Form Tests
-- ============================================================================

/--
info: Std.Http.RequestTarget.authorityForm
  { userInfo := none, host := Std.Http.URI.Host.name "proxy.example.com", port := Std.Http.URI.Port.value 3128 }
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "proxy.example.com:3128"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.authorityForm
  { userInfo := none, host := Std.Http.URI.Host.ipv4 127.0.0.1, port := Std.Http.URI.Port.value 8080 }
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "127.0.0.1:8080"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.authorityForm
  { userInfo := none, host := Std.Http.URI.Host.name "1example.com", port := Std.Http.URI.Port.value 8080 }
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "1example.com:8080"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.absoluteForm
  { scheme := "http",
    authority := some { userInfo := none,
                   host := Std.Http.URI.Host.name "1example.com",
                   port := Std.Http.URI.Port.omitted },
    path := { segments := #["path"], absolute := true },
    query := none,
    fragment := none }
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "http://1example.com/path"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.absoluteForm
  { scheme := "http",
    authority := some { userInfo := none,
                   host := Std.Http.URI.Host.name "123abc.example.com",
                   port := Std.Http.URI.Port.omitted },
    path := { segments := #["page"], absolute := true },
    query := none,
    fragment := none }
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "http://123abc.example.com/page"
  IO.println (repr result)

-- parseScheme: first byte uses `satisfy isAlphaByte` (not `takeWhile1AtMost`).
-- Schemes that start with a non-alpha byte must be rejected.
#eval parseCheckFail "1http://example.com/path"
#eval parseCheckFail "+http://example.com/path"
#eval parseCheckFail "-http://example.com/path"
#eval parseCheckFail ".http://example.com/path"

-- Scheme body allows '+', '-', '.'.
#eval parseCheck "coap+tcp://example.com/path"
#eval parseCheck "svn+ssh://example.com/path"
#eval parseCheck "my.scheme://example.com/path"
#eval parseCheck "a-b://example.com/path"

-- Single-letter scheme is valid.
#eval parseCheck "a://example.com/path"

-- parsePortNumber now uses `takeWhileAtMost` (succeeds at EOF) instead of
-- `takeWhileUpTo1` (would fail with .eof). Verify a port at the very end of
-- the input still parses correctly.
#guard
  match (parseRequestTarget <* Std.Internal.Parsec.eof).run "example.com:8080".toUTF8 with
  | .ok (.authorityForm auth) => auth.port == .value 8080
  | _ => false

-- Port 0 is technically valid (toNat? succeeds).
#guard
  match (parseRequestTarget <* Std.Internal.Parsec.eof).run "example.com:0".toUTF8 with
  | .ok (.authorityForm auth) => auth.port == .value 0
  | _ => false

-- Port > 65535 must be rejected. Use an unambiguous authority URL so the
-- number is definitely parsed as a port, not as a path segment.
#eval parseCheckFail "http://example.com:65536/path"
#eval parseCheckFail "http://example.com:99999/path"

-- parseQuery now uses `split '&'` instead of `splitOn "&"`.
-- A trailing `&` is accepted and produces an empty-key entry; it is not a
-- parse failure.
#guard
  match (parseRequestTarget <* Std.Internal.Parsec.eof).run "/path?key=val&".toUTF8 with
  | .ok result => result.query.size == 2
  | .error _ => false

-- A value may contain an unencoded `=`: the name ends at the first `=` (#16021).
/--
info: some (some "a=b")
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "/path?key=a=b"
  IO.println (repr (result.query.find? "key"))

-- A percent-encoded `=` in the value is fine; `%3D` is preserved as-is in
-- the EncodedQueryParam.
/--
info: some (some "a%3Db")
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "/path?key=a%3Db"
  IO.println (repr (result.query.find? "key"))

-- IPv4/IPv6 parsing now uses `takeWhile1AtMost` (still requires ≥1 byte).
-- Both types continue to work at the very end of the input.
#guard
  match (parseRequestTarget <* Std.Internal.Parsec.eof).run "192.168.0.1:80".toUTF8 with
  | .ok (.authorityForm auth) => toString auth.host == "192.168.0.1"
  | _ => false

#guard
  match (parseRequestTarget <* Std.Internal.Parsec.eof).run "http://[::1]/".toUTF8 with
  | .ok (.absoluteForm uri) => uri.authority.any fun a => match a.host with | .ipv6 _ => true | _ => false
  | _ => false

-- RFC 3986 §3.2 allows an empty reg-name, so `file:///path` (empty authority)
-- must parse as an absolute URI, not fall back to a relative reference.
-- This ensures the non-http(s) scheme guard in redirect logic fires correctly.
#guard
  match URIReference.parse? "file:///etc/passwd" with
  | some (.absolute af) => af.scheme.val == "file" && af.host?.isNone && toString af == "file:///etc/passwd"
  | _ => false

-- `none` means no query delimiter, while `some .empty` means an explicit empty query.
#guard (URI.parse! "http://example.com/path").query.isNone

#guard
  match (URI.parse! "http://example.com/path?").query with
  | some q => q.isEmpty && toString (URI.parse! "http://example.com/path?") == "http://example.com/path?"
  | none => false

#guard
  match RequestTarget.parse? "/path?" with
  | some (.originForm _ (some q)) => q.isEmpty && toString (RequestTarget.parse! "/path?") == "/path?"
  | _ => false

#guard
  match URIReference.parse? "?" with
  | some (.relative ref) => ref.query.isSome && toString (URIReference.parse! "?") == "?"
  | _ => false

#guard
  match URIReference.parse? "#frag" with
  | some (.relative ref) => ref.query.isNone && toString (URIReference.parse! "#frag") == "#frag"
  | _ => false

-- ============================================================================
-- Hosts
-- ============================================================================

private def hostOf (s : String) : Option URI.Host :=
  (URI.parse? s).bind (·.host?)

-- A percent-encoded registered name is decoded (RFC 3986 §3.2.2, §6.2.2.2).
#guard (hostOf "http://ex%41mple.com/").map toString == some "example.com"

-- The host is an IPv4 address only when the whole decoded host is one, so a percent-encoded address
-- is that address, and printing it and parsing it again gives the same host.
#guard
  match hostOf "http://127.0.0.%31/" with
  | some (.ipv4 addr) => toString addr == "127.0.0.1"
  | _ => false

#guard
  match URI.parse? "http://%31%32%37.0.0.1/" with
  | some u => (URI.parse? (toString u)).bind (·.host?) == u.host?
  | none => false

-- `_` is a reg-name character; container service names use it. A dotted quad followed by `_svc` is
-- a name, not an address with trailing bytes.
#guard (hostOf "http://_svc.local/").map toString == some "_svc.local"
#guard
  match hostOf "http://10.0.0.1_svc/" with
  | some (.name n) => toString n == "10.0.0.1_svc"
  | _ => false

-- A fully qualified name ends in a single `.`, which adds no label.
#guard (URI.DomainName.ofString? "example.com.").isSome
#guard (hostOf "http://example.com./").map toString == some "example.com."
#guard (URI.DomainName.ofString? "example.com..").isNone

-- The system resolver reads a name whose last label is a number as an IPv4 address in shorthand
-- (`127.1` is `127.0.0.1`), so such a name is not a domain name.
#eval show IO Unit from do
  for host in ["127.1", "2130706433", "0x7f.0.0.1", "1.2.3", "example.0x1F", "127.1."] do
    if let some u := URI.parse? s!"http://{host}/" then
      throw <| IO.userError s!"http://{host}/ parsed with host {repr u.host?}"
    if (URI.DomainName.ofString? host).isSome then
      throw <| IO.userError s!"{host} is accepted as a domain name"
  for host in ["1.example", "example.com1", "a.b1c", "0x1g"] do
    unless hostOf s!"http://{host}/" matches some (.name _) do
      throw <| IO.userError s!"http://{host}/ does not parse with a domain name host"

-- ============================================================================
-- Request targets and references
-- ============================================================================

-- RFC 9112 §3.2.1: an origin-form target is never empty, even for a URI with no path.
#guard toString (URI.parse! "http://example.com").originTarget == "/"
#guard toString (URI.parse! "http://example.com?q=1").originTarget == "/?q=1"

-- A name containing `=` is percent-encoded, so it still reads back as the name.
#guard toString (URI.EncodedQueryParam.encode "a=b") == "a%3Db"
#guard
  let uri := URI.Builder.empty
    |>.setScheme! "http" |>.setHost! "example.com" |>.addQueryParam "k=1" "v=2" |>.build
  ((URI.parse? (toString uri)).bind (·.query)).bind (·.get "k=1") == some "v=2"

-- `http:////evil.com/x` has an empty authority and so names no host. The empty authority is printed
-- again (RFC 3986 §5.3), so the path is not read as `//evil.com`, which names another host.
#guard
  match URI.parse? "http:////evil.com/x" with
  | some u => u.host?.isNone && toString u == "http:////evil.com/x" &&
      (URI.parse? (toString u)).any (·.host?.isNone)
  | none => false

-- RFC 9110 §4.2.1: an http(s) request target with an empty host is rejected.
#eval parseCheckFail "http:///x"
#eval parseCheckFail "https:///x?q"
#eval parseCheckFail "http:////evil.com/x"
#guard (RequestTarget.parse? "file:///etc/passwd").isSome

-- A reference that starts with `//` has an authority; it is never read as a path when the
-- authority does not parse.
#guard (URIReference.parse? "//a:b/x").isNone
#guard (URIReference.parse? "//a:1/x").isSome

-- RFC 3986 §4.2: the first segment of a relative path cannot contain `:`, or it would read as a
-- scheme.
#guard (URIReference.parse? "1:b").isNone
#guard (URIReference.parse? "./1:b").isSome
#guard (URIReference.parse? "a/1:b").isSome

-- A fragment whose decoded bytes are not UTF-8 is kept, with U+FFFD for the invalid bytes.
#guard (URI.parse? "http://example.com/#caf%E9").bind (·.fragment) == some "caf�"
#guard
  match URIReference.parse? "/x#caf%E9" with
  | some (.relative ref) => ref.fragment == some "caf�"
  | _ => false
#guard
  match URIReference.parse? "http://example.com/#caf%E9" with
  | some (.absolute uri) => uri.fragment == some "caf�"
  | _ => false

-- ============================================================================
-- Percent-encoded hosts in request targets and `Host`
-- ============================================================================

-- A request target and a `Host` header take the RFC 3986 `host` (RFC 9110 §7.2, RFC 9112 §3.2), so a
-- percent-encoded name is decoded there as in any URI or reference.
#eval parseCheck "http://ex%41mple.com/x" "http://example.com/x"
#eval parseCheck "ex%41mple.com:443" "example.com:443"
#guard
  match (parseHostHeader <* Std.Internal.Parsec.eof).run "ex%41mple.com:8080".toUTF8 with
  | .ok (host, port) => toString host == "example.com" && port == .value 8080
  | .error _ => false
-- Decoding does not let through what the name itself could not hold.
#eval parseCheckFail "http://exa%2Fmple.com/x"
#guard ((parseHostHeader <* Std.Internal.Parsec.eof).run "exa%00mple.com".toUTF8).toOption.isNone
#guard
  match URIReference.parse? "//ex%41mple.com/x" with
  | some (.relative r) => r.authority.map (toString ·.host) == some "example.com"
  | _ => false

-- ============================================================================
-- Query names containing `=`
-- ============================================================================

-- A name's `=` is printed escaped, or it would end the name when the query is read back. A value
-- keeps its `=` as is.
#guard
  match URI.EncodedQueryParam.fromString? "a=b", URI.EncodedQueryParam.fromString? "c=d" with
  | some key, some value =>
    let printed := toString (URI.Query.empty.insertEncoded key (some value))
    printed == "?a%3Db=c=d" &&
      (RequestTarget.parse? ("/p" ++ printed)).map (·.query.get "a=b") == some (some "c=d")
  | _, _ => false

#guard
  match URI.EncodedQueryParam.ofByteArray? "=".toUTF8 with
  | some key =>
    let printed := toString (URI.Query.empty.insertEncoded key none)
    printed == "?%3D" && (RequestTarget.parse? ("/p" ++ printed)).map (·.query.contains "=") == some true
  | none => false

-- ============================================================================
-- Builder hosts
-- ============================================================================

-- `setHost?` takes a dotted-quad IPv4 address as that address, as a parsed URI does, and still
-- refuses a name that ends in a number.
#guard
  match URI.Builder.empty.setScheme! "http" |>.setHost? "127.0.0.1" with
  | some b =>
    let u := b.build
    toString u == "http://127.0.0.1/" && u.host? == (URI.parse! "http://127.0.0.1/").host?
  | none => false
#guard (URI.Builder.empty.setHost? "127.1").isNone
#guard (URI.Builder.empty.setHost? "1.2.3.4.5").isNone
#guard
  match (URI.Builder.empty.setHost? "localhost").bind (·.build.host?) with
  | some (.name n) => toString n == "localhost"
  | _ => false

-- ============================================================================
-- Printing reads back as the same components
-- ============================================================================

private def relRef? (s : String) : Option URI.RelativeRef :=
  match URIReference.parse? s with
  | some (.relative r) => some r
  | _ => none

private def mkPath (segments : List String) (absolute : Bool) : URI.Path :=
  { segments := (segments.map URI.EncodedSegment.encode).toArray, absolute }

-- Removing dot segments can leave a path that begins with `//` and no authority, and so can a
-- builder with no host.
#guard
  let u := (URI.parse! "http:/.//evil.com/x").normalize
  toString u == "http:/.//evil.com/x" && (URI.parse? (toString u)).any (·.host?.isNone)
#guard
  let u := URI.Builder.empty |>.setScheme! "http" |>.setPath #["", "evil.com"] |>.build
  (URI.parse? (toString u)).any (·.host?.isNone)

-- An empty authority before such a path (`file:////host/share`, RFC 8089 Appendix E.3.2) parses.
#guard
  match URI.parse? "file:////host/share" with
  | some u => u.host?.isNone && toString u == "file:////host/share" &&
      (URI.parse? (toString u)).map (·.path.normalize) == some u.path
  | none => false

-- The same holds for a reference, where `//` would read as an authority.
#guard
  match relRef? "/.//evil.com/x" with
  | some r =>
    let r := { r with path := r.path.normalize }
    toString r == "/.//evil.com/x" && (relRef? (toString r)).any (·.authority.isNone)
  | none => false

-- RFC 3986 §4.2: in a reference, a first segment with `:` would read as a scheme, so it is printed
-- behind a `./` segment.
#guard
  match relRef? "./a:b" with
  | some r =>
    let r := { r with path := r.path.normalize }
    toString r == "./a:b" && (relRef? (toString r)).isSome
  | none => false

-- A relative path that begins with an empty segment would print as an absolute path.
#guard
  let r : URI.RelativeRef := { authority := none, path := mkPath ["", "x"] false, fragment := none }
  toString r == ".//x" && (relRef? (toString r)).any (·.path.normalize == r.path)

-- After an authority, and in origin-form, a non-empty path begins with `/`, or it would extend the
-- host.
#guard
  let u := (URI.parse! "http://example.com").withPath (mkPath ["evil"] false)
  toString u == "http://example.com/evil" && (URI.parse? (toString u)).bind (·.host?) == u.host?
#guard toString (RequestTarget.originForm (mkPath ["x"] false) none) == "/x"

-- Every path over a few segment shapes, in a URI and in a reference, with and without an authority,
-- prints as a string that reads back with the same authority and, once dot segments are removed,
-- the same path.
private def segmentLists (shapes : List String) : Nat → List (List String)
  | 0 => [[]]
  | n + 1 => [] :: shapes.flatMap fun s => (segmentLists shapes n).map (s :: ·)

#eval show IO Unit from do
  let authorities : List (Option URI.Authority) :=
    [none, (URI.parse! "foo://host").authority]
  let render (path : URI.Path) (authority : Option URI.Authority) (scheme : Bool) : String :=
    path.normalize.render authority.isSome scheme
  for segments in segmentLists ["", ".", "..", "a", "a:b"] 3 do
    for absolute in [false, true] do
      let path := mkPath segments absolute
      for authority in authorities do
        -- After an authority a non-empty path can only be absolute.
        let meant :=
          if authority.isSome && !(toString path).isEmpty then { path with absolute := true } else path
        let uri : URI :=
          { scheme := URI.Scheme.ofString! "foo", authority, path, query := none, fragment := none }
        match URI.parse? (toString uri) with
        | some back =>
          unless back.authority == authority && render back.path authority true == render meant authority true do
            throw <| IO.userError s!"URI {repr path} printed as {toString uri} reads back as {repr back}"
        | none => throw <| IO.userError s!"URI {repr path} printed as {toString uri} does not parse"
        let ref : URI.RelativeRef := { authority, path, fragment := none }
        match relRef? (toString ref) with
        | some back =>
          unless back.authority == authority && render back.path authority false == render meant authority false do
            throw <| IO.userError s!"reference {repr path} printed as {toString ref} reads back as {repr back}"
        | none => throw <| IO.userError s!"reference {repr path} printed as {toString ref} does not parse"
