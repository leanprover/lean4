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
#eval parseCheck "localhost:65535"
#eval parseCheck "http:80"
#eval parseCheck "https://user:pass@secure.example.com/private"
#eval parseCheck "/double//slash//path"
#eval parseCheck "http://user%40example:pass%3Aword@host.com"
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
#eval parseCheckFail "http://exa_mple.com/path"
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
    query := #[],
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
    query := #[],
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
    query := #[],
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

-- Raw lookup APIs should not alias with pre-encoded key spellings.
#guard
  match (parseRequestTarget <* Std.Internal.Parsec.eof).run "/api?%61=1&a=2".toUTF8 with
  | .ok result =>
      let encodedA? := EncodedQueryParam.fromString? "%61"
      ((result.query.find? "a" |>.bind id |>.bind EncodedQueryParam.decode) == some "2") &&
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
          erasedRaw.containsEncoded encodedA &&
          !erasedEncoded.containsEncoded encodedA &&
          erasedEncoded.contains "a"
      | none => false
  | .error _ => false

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
    query := #[],
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
    query := #[],
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

-- parseQuery uses `split '='` instead of `splitOn "="`.
-- A pair containing more than one unencoded `=` must be rejected because the
-- three-element split falls into the error branch.
#eval parseCheckFail "/path?key=a=b"

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
