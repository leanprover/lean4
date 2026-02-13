/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
import Std.Internal.Http.Data.URI
import Std.Internal.Http.Data.URI.Encoding

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
#eval IO.println (repr (EncodedQueryString.ofByteArray? (r := isQueryChar) "hello+world".toUTF8))

/--
info: none
-/
#guard_msgs in
#eval IO.println (repr (EncodedQueryString.ofByteArray? (r := isQueryChar) "%".toUTF8))

/--
info: some "hello world"
-/
#guard_msgs in
#eval IO.println (repr <| EncodedQueryString.decode (r := isQueryChar) =<< (EncodedQueryString.ofByteArray? (r := isQueryChar) "hello+world".toUTF8))

/--
info: some " "
-/
#guard_msgs in
#eval IO.println (repr <| EncodedQueryString.decode (r := isQueryChar) =<< (EncodedQueryString.ofByteArray? (r := isQueryChar) "%20".toUTF8))

-- ============================================================================
-- Request Target Parsing - Basic Tests
-- ============================================================================

#eval parseCheck "/path/with/encoded%20space"
#eval parseCheck "/path/with/encoded%20space/"
#eval parseCheck "*"
#eval parseCheck "/api/search?q=hello%20world&category=tech%2Bgames"
#eval parseCheck "/"
#eval parseCheck "/api/v1/users/123/posts/456/comments/789"
#eval parseCheck "/files/../etc/passwd"
#eval parseCheck "example.com:8080"
#eval parseCheck "https://example.com:8080/ata"
#eval parseCheck "192.168.1.1:3000"
#eval parseCheck "[::1]:8080"
#eval parseCheck "http://example.com/path/to/resource?query=value"
#eval parseCheck "https://api.example.com:443/v1/users?limit=10"
#eval parseCheck "http://[2001:db8::1]:8080/path"
#eval parseCheck "https://xn--nxasmq6b.xn--o3cw4h/path"
#eval parseCheck "localhost:65535"
#eval parseCheck "https://user:pass@secure.example.com/private"
#eval parseCheck "/double//slash//path"
#eval parseCheck "http://user%40example:pass%3Aword@host.com"

-- Parse failure tests
#eval parseCheckFail "/path with space"
#eval parseCheckFail "/path/%"
#eval parseCheckFail "/path/%2"
#eval parseCheckFail "/path/%ZZ"
#eval parseCheckFail ""
#eval parseCheckFail "[::1"
#eval parseCheckFail "[:::1]:80"
#eval parseCheckFail "#frag"
#eval parseCheckFail "/path/\n"
#eval parseCheckFail "/path/\u0000"

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
info: Std.Http.RequestTarget.asteriskForm
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "*"
  IO.println (repr result)

/--
info: none
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "https://ata/b?ata=be"
  IO.println (repr (result.fragment?))

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
  { userInfo := none, host := Std.Http.URI.Host.name "example.com", port := some 8080 }
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "example.com:8080"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.authorityForm { userInfo := none, host := Std.Http.URI.Host.ipv4 192.168.1.1, port := some 3000 }
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "192.168.1.1:3000"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.authorityForm { userInfo := none, host := Std.Http.URI.Host.ipv6 ::1, port := some 8080 }
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "[::1]:8080"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.absoluteForm
  { scheme := "https",
    authority := some { userInfo := none, host := Std.Http.URI.Host.name "example.com", port := some 8080 },
    path := { segments := #["ata"], absolute := true },
    query := #[],
    fragment := none }
  _
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "https://example.com:8080/ata"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.absoluteForm
  { scheme := "http",
    authority := some { userInfo := none, host := Std.Http.URI.Host.ipv6 2001:db8::1, port := some 8080 },
    path := { segments := #["path"], absolute := true },
    query := #[],
    fragment := none }
  _
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "http://[2001:db8::1]:8080/path"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.absoluteForm
  { scheme := "https",
    authority := some { userInfo := some { username := "user b", password := some "pass" },
                   host := Std.Http.URI.Host.name "secure.example.com",
                   port := none },
    path := { segments := #["private"], absolute := true },
    query := #[],
    fragment := none }
  _
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
info: some { username := "user only", password := none }
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
info: some { username := "user", password := some "p@ss:w0rd" }
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

/--
info: /a
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

/--
info: /a/b/c
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

#guard ((URI.parse! "http://example.com").withScheme "htTps" |>.scheme) == "https"
#guard ((URI.parse! "http://example.com").withScheme "ftP" |>.scheme) == "ftp"

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

-- ============================================================================
-- Query Operations
-- ============================================================================

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

/--
info: none
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "/path"
  IO.println (repr result.fragment?)

-- ============================================================================
-- URI Builder Tests
-- ============================================================================

/--
info: https://example.com/api/users?page=1
-/
#guard_msgs in
#eval do
  let uri := URI.Builder.empty
    |>.setScheme "https"
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
    |>.setScheme "http"
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
    |>.setScheme "https"
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
  { userInfo := none, host := Std.Http.URI.Host.name "proxy.example.com", port := some 3128 }
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "proxy.example.com:3128"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.authorityForm { userInfo := none, host := Std.Http.URI.Host.ipv4 127.0.0.1, port := some 8080 }
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "127.0.0.1:8080"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.authorityForm
  { userInfo := none, host := Std.Http.URI.Host.name "1example.com", port := some 8080 }
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "1example.com:8080"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.absoluteForm
  { scheme := "http",
    authority := some { userInfo := none, host := Std.Http.URI.Host.name "1example.com", port := none },
    path := { segments := #["path"], absolute := true },
    query := #[],
    fragment := none }
  _
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "http://1example.com/path"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.absoluteForm
  { scheme := "http",
    authority := some { userInfo := none, host := Std.Http.URI.Host.name "123abc.example.com", port := none },
    path := { segments := #["page"], absolute := true },
    query := #[],
    fragment := none }
  _
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser parseRequestTarget "http://123abc.example.com/page"
  IO.println (repr result)
