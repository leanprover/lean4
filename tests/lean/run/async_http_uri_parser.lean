import Std.Internal.Http.Protocol.H1.Parser

open Std.Http.Protocol

def runParser (parser : Std.Internal.Parsec.ByteArray.Parser α) (s : String) : IO α :=
  IO.ofExcept (parser.run s.toUTF8)

-- Basic forms test (existing)
/--
info: Std.Http.RequestTarget.originForm { segments := #["path", "with", "encoded space"], absolute := true } none
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Parser.parseRequestTarget "/path/with/encoded%20space"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.originForm { segments := #["path", "with", "encoded space"], absolute := false } none
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Parser.parseRequestTarget "path/with/encoded%20space"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.asteriskForm
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Parser.parseRequestTarget "*"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.absoluteForm
  { scheme := some "https",
    authority := some { userInfo := none, host := Std.Http.URI.Host.name "ata", port := none },
    path := { segments := #["b"], absolute := true },
    query := some #[("ata", some "be")],
    fragment := some "lol" }
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Parser.parseRequestTarget "https://ata/b?ata=be#lol"
  IO.println (repr result)
/--
info: Std.Http.RequestTarget.originForm
  { segments := #["api", "search"], absolute := true }
  (some #[("q", some "hello world"), ("category", some "tech+games")])
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Parser.parseRequestTarget "/api/search?q=hello%20world&category=tech%2Bgames"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.originForm { segments := #["files", "my document.pdf"], absolute := true } none
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Parser.parseRequestTarget "/files/my%20document%2Epdf"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.originForm
  { segments := #["search"], absolute := true }
  (some #[("name", some "✓ checked"), ("emoji", some "😀")])
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Parser.parseRequestTarget "/search?name=%E2%9C%93%20checked&emoji=%F0%9F%98%80"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.originForm
  { segments := #["api"], absolute := true }
  (some #[("param1", some "value1"), ("param2", some "value2"), ("param3", some "value3")])
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Parser.parseRequestTarget "/api?param1=value1&param2=value2&param3=value3"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.originForm
  { segments := #["search"], absolute := true }
  (some #[("debug", none), ("verbose", none), ("q", some "test")])
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Parser.parseRequestTarget "/search?debug&verbose&q=test"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.originForm
  { segments := #["api"], absolute := true }
  (some #[("empty", some ""), ("also_empty", some ""), ("has_value", some "something")])
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Parser.parseRequestTarget "/api?empty=&also_empty=&has_value=something"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.originForm
  { segments := #["search"], absolute := true }
  (some #[("q", some "cats&dogs"), ("filter", some "name=max")])
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Parser.parseRequestTarget "/search?q=cats%26dogs&filter=name%3Dmax"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.originForm { segments := #[], absolute := true } none
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Parser.parseRequestTarget "/"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.originForm
  { segments := #["api", "v1", "users", "123", "posts", "456", "comments", "789"], absolute := true }
  none
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Parser.parseRequestTarget "/api/v1/users/123/posts/456/comments/789"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.originForm { segments := #["files", "..", "etc", "passwd"], absolute := true } none
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Parser.parseRequestTarget "/files/../etc/passwd"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.originForm { segments := #["path/with/encoded/slashes"], absolute := true } none
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Parser.parseRequestTarget "/path%2Fwith%2Fencoded%2Fslashes"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.absoluteForm
  { scheme := some "example.com",
    authority := none,
    path := { segments := #["8080"], absolute := false },
    query := none,
    fragment := none }
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Parser.parseRequestTarget "example.com:8080"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.authorityForm
  { userInfo := none, host := Std.Http.URI.Host.name "example.com", port := some 8080 }
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Parser.parseRequestTarget "example.com:8080"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.authorityForm { userInfo := none, host := Std.Http.URI.Host.ipv4 192.168.1.1, port := some 3000 }
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Parser.parseRequestTarget "192.168.1.1:3000"
  IO.println (repr result)

/--
info: Std.Http.RequestTarget.authorityForm { userInfo := none, host := Std.Http.URI.Host.ipv6 ::1, port := some 8080 }
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Parser.parseRequestTarget "[::1]:8080"
  IO.println (repr result)

-- Absolute form tests
/--
info: Std.Http.RequestTarget.originForm
  { segments := #["path", "to", "resource"], absolute := true }
  (some #[("query", some "value")])
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Parser.parseRequestTarget "http://example.com/path/to/resource?query=value"
  IO.println (repr result)

/--
info:
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Parser.parseRequestTarget "https://api.example.com:443/v1/users?limit=10"
  IO.println (repr result)

/--
Absolute form with userinfo
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Parser.parseRequestTarget "https://user:pass@secure.example.com/private"
  IO.println (repr result)

/--
Absolute form with IPv6 host
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Parser.parseRequestTarget "http://[2001:db8::1]:8080/path"
  IO.println (repr result)

-- Fragment tests (though fragments shouldn't appear in request targets)
/--
Absolute form with fragment
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Parser.parseRequestTarget "https://example.com/page#section1"
  IO.println (repr result)

-- Edge cases and malformed inputs
/--
Just a query string
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Parser.parseRequestTarget "?query=only"
  IO.println (repr result)

/--
Path with consecutive slashes
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Parser.parseRequestTarget "//double//slash//path"
  IO.println (repr result)

/--
Very long path with encoding
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Parser.parseRequestTarget "/very/long/path/with/many/segments/and/encoded%20spaces/and%2Bplus%2Bsigns/final%2Fsegment"
  IO.println (repr result)

/--
Complex query with arrays and objects (URL encoded)
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Parser.parseRequestTarget "/api?filters%5B%5D=active&filters%5B%5D=verified&sort%5Bname%5D=asc&sort%5Bdate%5D=desc"
  IO.println (repr result)

/--
Path with international domain name encoding
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Parser.parseRequestTarget "https://xn--nxasmq6b.xn--o3cw4h/path"
  IO.println (repr result)

/--
Authority with non-standard port
-/
#guard_msgs in
#eval show IO _ from do
  let result ← runParser Std.Http.Parser.parseRequestTarget "localhost:65535"
  IO.println (repr result)
