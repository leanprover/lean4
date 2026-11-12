module

import Std.Http.Test.Helpers
import Std.Http.Data.URI.Encoding

/-!
# URI parsing

How `Std.Http.URI` reads percent-encoded components, request-targets, schemes, userinfo, ports, hosts
and URI references, and which inputs it rejects. RFC 3986 §2–§4, RFC 9112 §3.2, RFC 9110 §4.2.1,
RFC 1034/1035/1123 for host names. Regressions: #16079.
-/

open Std Http
open Std.Http.URI
open Std.Http.URI.Parser
open Std.Http.Internal.Test

private def target? (s : String) : Option RequestTarget :=
  ((parseRequestTarget <* Std.Internal.Parsec.eof).run s.toUTF8).toOption

private def hostHeader? (s : String) : Option (URI.Host × URI.Port) :=
  ((parseHostHeader <* Std.Internal.Parsec.eof).run s.toUTF8).toOption

private def hostOf (s : String) : Option URI.Host :=
  (URI.parse? s).bind (·.host?)

/-- Fails unless `s` parses as a request-target whose `repr` is `want`. -/
private def expectTarget (s want : String) : IO Unit :=
  match target? s with
  | some t => expectEq s (reprLine t) want
  | none => throw <| IO.userError s!"{s.quote} did not parse"

/-- Fails unless `s` parses as a request-target that prints as `exact`. -/
private def expectPrints (s : String) (exact : String := s) : IO Unit :=
  match target? s with
  | some t => expectEq s (toString t) exact
  | none => throw <| IO.userError s!"{s.quote} did not parse"

private def expectRejected (s : String) : IO Unit :=
  match target? s with
  | some t => throw <| IO.userError s!"expected parse failure, but succeeded with {reprLine t}"
  | none => pure ()

private def repeatStr (s : String) (n : Nat) : String := String.join (List.replicate n s)

/-! ## Percent-encoded components (RFC 3986 §2.1) -/

#eval checkCases "Valid percent encoding validation" #[
    ("abc", "abc", "some \"abc\""),
    ("%20", "%20", "some \"%20\""),
    ("hello%20world", "hello%20world", "some \"hello%20world\""),
    ("%FF", "%FF", "some \"%FF\""),
    ("%00", "%00", "some \"%00\"")
  ] fun (label, s, want) => expectEq label (reprLine (EncodedSegment.ofByteArray? s.toUTF8)) want

#eval checkCases "Invalid percent encoding: incomplete or non-hex escape" #[
    ("incomplete: %", "%"),
    ("incomplete: hello%", "hello%"),
    ("incomplete: %2", "%2"),
    ("incomplete: %A", "%A"),
    ("non-hex: %GG", "%GG"),
    ("non-hex: %2G", "%2G"),
    ("non-hex: %G2", "%G2")
  ] fun (label, s) => expectEq label (reprLine (EncodedSegment.ofByteArray? s.toUTF8)) "none"

#eval checkCases "Percent Encoding Decode Tests" #[
    ("abc", "abc", "some \"abc\""),
    ("%20", "%20", "some \" \""),
    ("hello%20world", "hello%20world", "some \"hello world\""),
    ("%20%21", "%20%21", "some \" !\""),
    ("%FF is not UTF-8 once decoded", "%FF", "none"),
    ("%00 decodes to NUL", "%00", "some \"\\x00\"")
  ] fun (label, s, want) =>
    expectEq label (reprLine (EncodedSegment.decode =<< EncodedSegment.ofByteArray? s.toUTF8)) want

#eval checkCases "A fragment whose decoded bytes are not UTF-8 is kept, with U+FFFD for the invalid bytes" #[
    ("URI.parse?", ensure ((URI.parse? "http://example.com/#caf%E9").bind (·.fragment) == some "caf�")
      "URI.parse? fragment"),
    ("relative reference", ensure (match URIReference.parse? "/x#caf%E9" with
      | some (.relative ref) => ref.fragment == some "caf�"
      | _ => false) "relative reference fragment"),
    ("absolute reference", ensure (match URIReference.parse? "http://example.com/#caf%E9" with
      | some (.absolute uri) => uri.fragment == some "caf�"
      | _ => false) "absolute reference fragment")
  ] (·.2)

#eval checkCases "Non-query components retain literal pluses (#15246)" #[
    ("EncodedSegment.encode", expectEq "segment" (toString (EncodedSegment.encode "+")) "+"),
    ("EncodedSegment.decode", expectEq "segment" (EncodedSegment.encode "+").decode (some "+")),
    ("EncodedFragment.encode", expectEq "fragment" (toString (EncodedFragment.encode "+")) "+"),
    ("EncodedUserInfo.encode", expectEq "userinfo" (toString (EncodedUserInfo.encode "+")) "+")
  ] (·.2)


private def isPchar (c : Char) : Bool :=
  c.isAlphanum || "-._~!$&'()*+,;=:@".contains c

private def pctHex (n : Nat) : String :=
  let d := Nat.toDigits 16 n |>.map Char.toUpper
  "%" ++ String.ofList (if d.length < 2 then '0' :: d else d)

#eval checkCases "`EncodedSegment.encode` keeps exactly the pchars (RFC 3986 §3.3)" #[
    ("every ASCII byte", do
      for n in List.range 128 do
        let s := String.singleton (Char.ofNat n)
        expectEq s!"encode byte {n}" (toString (EncodedSegment.encode s))
          (if isPchar (Char.ofNat n) then s else pctHex n)
        expectEq s!"decode byte {n}" (EncodedSegment.encode s).decode (some s)),
    ("/ → %2F", expectEq "encode" (toString (EncodedSegment.encode "/")) "%2F"),
    ("% → %25", expectEq "encode" (toString (EncodedSegment.encode "%")) "%25"),
    ("SP → %20", expectEq "encode" (toString (EncodedSegment.encode " ")) "%20"),
    ("every byte of a non-ASCII character", do
      expectEq "encode" (toString (EncodedSegment.encode "é✓")) "%C3%A9%E2%9C%93"
      expectEq "decode" (EncodedSegment.encode "é✓").decode (some "é✓"))
  ] (·.2)

#eval checkCases "`Path.toDecodedSegments` (RFC 3986 §2.1, §2.2)" #[
    ("a%20b", "/a%20b", #["a b"]),
    ("an encoded `/` stays inside its segment", "/c%2Fd", #["c/d"]),
    ("UTF-8", "/%E2%9C%93.txt", #["✓.txt"])
  ] fun (label, path, want) => expectEq label (URI.parse! s!"http://example.com{path}").path.toDecodedSegments want

/-! ## Request-target forms (RFC 9112 §3.2) -/

#eval checkCases "Request Target Parsing - Detailed Output Tests" #[
    ("/path/with/encoded%20space", "/path/with/encoded%20space",
      "Std.Http.RequestTarget.originForm { segments := #[\"path\", \"with\", \"encoded%20space\"], absolute := true } none"),
    ("///path/with/encoded%20space", "///path/with/encoded%20space",
      "Std.Http.RequestTarget.originForm { segments := #[\"\", \"\", \"path\", \"with\", \"encoded%20space\"], absolute := true } none"),
    ("*", "*", "Std.Http.RequestTarget.asteriskForm"),
    ("query values stay encoded", "/api/search?q=hello%20world&category=tech%2Bgames",
      "Std.Http.RequestTarget.originForm { segments := #[\"api\", \"search\"], absolute := true } (some #[(\"q\", some \"hello%20world\"), (\"category\", some \"tech%2Bgames\")])"),
    ("/", "/", "Std.Http.RequestTarget.originForm { segments := #[], absolute := true } none"),
    ("example.com:8080", "example.com:8080",
      "Std.Http.RequestTarget.authorityForm { userInfo := none, host := Std.Http.URI.Host.name \"example.com\", port := Std.Http.URI.Port.value 8080 }"),
    ("192.168.1.1:3000", "192.168.1.1:3000",
      "Std.Http.RequestTarget.authorityForm { userInfo := none, host := Std.Http.URI.Host.ipv4 192.168.1.1, port := Std.Http.URI.Port.value 3000 }"),
    ("http:80 is authority-form", "http:80",
      "Std.Http.RequestTarget.authorityForm { userInfo := none, host := Std.Http.URI.Host.name \"http\", port := Std.Http.URI.Port.value 80 }"),
    ("[::1]:8080", "[::1]:8080",
      "Std.Http.RequestTarget.authorityForm { userInfo := none, host := Std.Http.URI.Host.ipv6 ::1, port := Std.Http.URI.Port.value 8080 }"),
    ("https://example.com:8080/ata", "https://example.com:8080/ata",
      "Std.Http.RequestTarget.absoluteForm { scheme := \"https\", authority := some { userInfo := none, host := Std.Http.URI.Host.name \"example.com\", port := Std.Http.URI.Port.value 8080 }, path := { segments := #[\"ata\"], absolute := true }, query := none, fragment := none }"),
    ("http://[2001:db8::1]:8080/path", "http://[2001:db8::1]:8080/path",
      "Std.Http.RequestTarget.absoluteForm { scheme := \"http\", authority := some { userInfo := none, host := Std.Http.URI.Host.ipv6 2001:db8::1, port := Std.Http.URI.Port.value 8080 }, path := { segments := #[\"path\"], absolute := true }, query := none, fragment := none }"),
    ("userinfo stays encoded", "https://user%20b:pass@secure.example.com/private",
      "Std.Http.RequestTarget.absoluteForm { scheme := \"https\", authority := some { userInfo := some { username := \"user%20b\", password := some \"pass\" }, host := Std.Http.URI.Host.name \"secure.example.com\", port := Std.Http.URI.Port.omitted }, path := { segments := #[\"private\"], absolute := true }, query := none, fragment := none }")
  ] fun (_, s, want) => expectTarget s want

#eval checkCases "Encoded Path Segment Tests" #[
    ("/path%2Fwith%2Fslashes", "/path%2Fwith%2Fslashes",
      "Std.Http.RequestTarget.originForm { segments := #[\"path%2Fwith%2Fslashes\"], absolute := true } none"),
    ("/file%20name.txt", "/file%20name.txt",
      "Std.Http.RequestTarget.originForm { segments := #[\"file%20name.txt\"], absolute := true } none"),
    ("/caf%C3%A9", "/caf%C3%A9",
      "Std.Http.RequestTarget.originForm { segments := #[\"caf%C3%A9\"], absolute := true } none")
  ] fun (_, s, want) => expectTarget s want

#eval checkCases "authority-form needs at least one port digit" #[
    ("authority-form with an empty port was accepted",
      ensure (!(RequestTarget.parse? "example.com:").any (· matches .authorityForm _)) "example.com:"),
    ("file:///etc/passwd", ensure ((RequestTarget.parse? "file:///etc/passwd").any (· matches .absoluteForm _))
      "file:///etc/passwd did not parse as absolute-form"),
    ("ws://example.com/", ensure ((RequestTarget.parse? "ws://example.com/").any (· matches .absoluteForm _))
      "ws://example.com/ did not parse as absolute-form"),
    ("urn:isbn:0451450523", ensure ((RequestTarget.parse? "urn:isbn:0451450523").any (· matches .absoluteForm _))
      "urn:isbn:0451450523 did not parse as absolute-form"),
    ("mailto:a@example.com", ensure ((RequestTarget.parse? "mailto:a@example.com").any (· matches .absoluteForm _))
      "mailto:a@example.com did not parse as absolute-form"),
    ("example.com:0080", ensure ((RequestTarget.parse? "example.com:0080").any (· matches .authorityForm _))
      "example.com:0080 did not parse as authority-form")
  ] (·.2)


#eval checkCases "Request-target forms of other schemes (RFC 9112 §3.2.2–§3.2.3)" #[
    ("ietf:rfc:2648 is absolute-form", ensure ((RequestTarget.parse? "ietf:rfc:2648").any (· matches .absoluteForm _))
      "ietf:rfc:2648 did not parse as absolute-form"),
    ("example.com:0080 is authority-form with port 80", ensure (match RequestTarget.parse? "example.com:0080" with
      | some (.authorityForm auth) => auth.port == .value 80
      | _ => false) "example.com:0080")
  ] (·.2)

/-! ## Rejected request-targets (RFC 9112 §3.2, RFC 9110 §4.2.1) -/

#eval checkCases "Parse failure tests" #[
    "/path with space",
    "/path/%",
    "/path/%2",
    "/path/%ZZ",
    "",
    "[::1",
    "[:::1]:80",
    "http://-example.com/path",
    "http://[fe80::1%25eth0]/path",
    "#frag",
    "/path/\n",
    "/path/\u0000",
    "/page#section",
    "/api/v1/users/[id]:action"
  ] expectRejected

#eval checkCases "RFC 9110 §4.2.1: an http(s) request target with an empty host is rejected" #[
    ("http:///x", expectRejected "http:///x"),
    ("https:///x?q", expectRejected "https:///x?q"),
    ("http:////evil.com/x", expectRejected "http:////evil.com/x"),
    ("file:///etc/passwd is accepted", ensure (RequestTarget.parse? "file:///etc/passwd").isSome
      "file:///etc/passwd was rejected")
  ] (·.2)


#eval checkCases "`URI.parse?` rejects control bytes and spaces (RFC 3986 §2, §3)" #[
    ("LF in the query", "http://example.com/?q\n"),
    ("CR in the scheme", "ht\rtp://example.com/"),
    ("DEL in the host", "http://exa\x7fmple.com/"),
    ("NUL in the path", "http://example.com/a\x00b"),
    ("TAB in the path", "http://example.com/a\tb"),
    ("%zz", "http://example.com/%zz"),
    (": alone", ":"),
    ("a leading SP", " http://example.com/"),
    ("SP in the scheme", "ht tp://example.com/"),
    ("SP in the host", "http://a b.com/"),
    ("an encoded SP after an empty IP literal", "http://[]%20%48%54%54%50/"),
    ("brackets and parentheses in the host", "hxxp://x[.]y(.)com:9059"),
    ("LF inside the URI", "http://example.com/a\nb"),
    ("a C0 control before the URI", "\x01http://example.com/"),
    ("a C0 control after the URI", "http://example.com/\x01"),
    ("SP after the URI", "http://example.com/ ")
  ] fun (label, s) => ensure (URI.parse? s).isNone s!"{label}: {s.quote} parsed"

/-! ## Scheme, userinfo and port (RFC 3986 §3.1, §3.2.1, §3.2.3) -/

#eval checkCases "UserInfo Tests" #[
    ("user:pass", "https://user:pass@example.com/private",
      "some { username := \"user\", password := some \"pass\" }"),
    ("user%20only", "https://user%20only@example.com/path",
      "some { username := \"user%20only\", password := none }"),
    (":pass", "https://:pass@example.com/path", "some { username := \"\", password := some \"pass\" }"),
    ("encoded password", "https://user:p%40ss%3Aw0rd@example.com/",
      "some { username := \"user\", password := some \"p%40ss%3Aw0rd\" }")
  ] fun (label, s, want) =>
    match (target? s).bind (·.authority?) with
    | some auth => expectEq label (reprLine auth.userInfo) want
    | none => throw <| IO.userError "no authority"

#eval checkCases "parseScheme: a scheme starts with ALPHA, and its body allows '+', '-', '.'" #[
    ("1http", expectRejected "1http://example.com/path"),
    ("+http", expectRejected "+http://example.com/path"),
    ("-http", expectRejected "-http://example.com/path"),
    (".http", expectRejected ".http://example.com/path"),
    ("coap+tcp", expectPrints "coap+tcp://example.com/path"),
    ("svn+ssh", expectPrints "svn+ssh://example.com/path"),
    ("my.scheme", expectPrints "my.scheme://example.com/path"),
    ("a-b", expectPrints "a-b://example.com/path"),
    ("Single-letter scheme is valid", expectPrints "a://example.com/path")
  ] (·.2)

#eval checkCases "Ports" #[
    ("a port at the very end of the input", ensure (match target? "example.com:8080" with
      | some (.authorityForm auth) => auth.port == .value 8080
      | _ => false) "example.com:8080"),
    ("Port 0 is technically valid", ensure (match target? "example.com:0" with
      | some (.authorityForm auth) => auth.port == .value 0
      | _ => false) "example.com:0"),
    ("Port > 65535 must be rejected: 65536", expectRejected "http://example.com:65536/path"),
    ("Port > 65535 must be rejected: 99999", expectRejected "http://example.com:99999/path"),
    ("Host example.com:000080", expectEq "Host example.com:000080"
      ((Header.Host.parse (.mk "example.com:000080")).map (·.port)) (some (.value 80))),
    ("URI with port 0000000000080", expectEq "port 0000000000080"
      ((URI.parse? "http://example.com:0000000000080/").bind (·.authority) |>.map (·.port))
      (some (.value 80))),
    ("port 00065536 was accepted", ensure (URI.parse? "http://example.com:00065536/").isNone
      "port 00065536 was accepted")
  ] (·.2)


#eval checkCases "Ports that are not `*DIGIT` up to 65535 are rejected (RFC 3986 §3.2.3)" #[
    ":namedport", ":%38%30", ":80:", ":foo", ":1.5", ":-1", ":0x10", ":-0", ":1_1", ": 1", ":1 ", ":६",
    ":65536"
  ] fun port => ensure (URI.parse? s!"http://example.com{port}/").isNone s!"port {port.quote} was accepted"

#eval checkCases "Port values" #[
    ("080 → 80", expectEq "port" ((URI.parse? "http://example.com:080/").map (·.authority.map (·.port)))
      (some (some (.value 80)))),
    ("an empty port before a path", expectEq "port" ((URI.parse? "http://192.168.0.2:/foo").map (·.authority.map (·.port)))
      (some (some .empty))),
    ("an empty port at the end", expectEq "port" ((URI.parse? "http://[::1]:").map (·.authority.map (·.port)))
      (some (some .empty))),
    ("an empty port is not an omitted one", do
      let some u := URI.parse? "http://[::1]:/foo/" | throw <| IO.userError "http://[::1]:/foo/ did not parse"
      ensure (u.authority.map (·.port) == some .empty && u.authority.map (·.port) != some .omitted)
        s!"port {reprLine (u.authority.map (·.port))}")
  ] (·.2)

#eval checkCases "Userinfo (RFC 3986 §3.2.1, §6.2.2.1)" #[
    ("a raw `@` in the password", ensure (URI.parse? "http://j@ne:p@ssword@host/").isNone
      "http://j@ne:p@ssword@host/ parsed"),
    ("a raw `@` in the username", ensure (URI.parse? "http://User@example.com:Pass@host/").isNone
      "http://User@example.com:Pass@host/ parsed"),
    ("a raw `^`", ensure (URI.parse? "http://us^er@host/").isNone "http://us^er@host/ parsed"),
    ("%3F and %40 stay encoded", ensure (match (URI.parse? "http://us%3Fer:p%40ss@host/").bind (·.authority) |>.bind (·.userInfo) with
      | some ui => toString ui.username == "us%3Fer" && ui.password.map toString == some "p%40ss"
      | none => false) "userinfo of http://us%3Fer:p%40ss@host/"),
    ("HTTP://User:Pass@HOST:080/", do
      let some u := URI.parse? "HTTP://User:Pass@HOST:080/" | throw <| IO.userError "did not parse"
      let ui := u.authority.bind (·.userInfo)
      ensure (ui.bind (·.username?) == some "User" && ui.bind (·.password?) == some "Pass") "userinfo split"
      ensure (u.authority.map (·.port) == some (.value 80)) "port 80"
      ensure (u.host?.map toString == some "host") "host lowercased"
      expectEq "normalized scheme" u.normalize.scheme.val "http")
  ] (·.2)

/-! ## Hosts (RFC 3986 §3.2.2, RFC 1034 §3.1, RFC 1123 §2.1) -/

#eval checkCases "A host that begins with an IPv4 address and goes on is a name (#16079)" #[
    ("1.2.3.4-x.example:443", expectTarget "1.2.3.4-x.example:443"
      "Std.Http.RequestTarget.authorityForm { userInfo := none, host := Std.Http.URI.Host.name \"1.2.3.4-x.example\", port := Std.Http.URI.Port.value 443 }"),
    ("http://1.2.3.4x.example/", ensure (match target? "http://1.2.3.4x.example/" with
      | some (.absoluteForm uri) => uri.authority.any fun a => toString a.host == "1.2.3.4x.example"
      | _ => false) "http://1.2.3.4x.example/"),
    ("Host 1.2.3.4-x.example:8080", ensure (match hostHeader? "1.2.3.4-x.example:8080" with
      | some (host, port) => toString host == "1.2.3.4-x.example" && port == .value 8080
      | none => false) "parseHostHeader 1.2.3.4-x.example:8080"),
    ("Host 1.2.3.4", ensure (match hostHeader? "1.2.3.4" with
      | some (.ipv4 _, .omitted) => true
      | _ => false) "parseHostHeader 1.2.3.4")
  ] (·.2)

#eval checkCases "IPv6 Host Tests" #[
    ("[::1]:8080", "[::1]:8080", "Std.Http.URI.Host.ipv6 ::1"),
    ("compressed", "http://[2001:db8::8a2e:370:7334]:8080/api", "Std.Http.URI.Host.ipv6 2001:db8::8a2e:370:7334"),
    ("[::]", "http://[::]/path", "Std.Http.URI.Host.ipv6 ::")
  ] fun (label, s, want) =>
    match (target? s).bind (·.authority?) with
    | some auth => expectEq label (reprLine auth.host) want
    | none => throw <| IO.userError "no authority"

#eval checkCases "Authority Form Tests" #[
    ("proxy.example.com:3128", "proxy.example.com:3128",
      "Std.Http.RequestTarget.authorityForm { userInfo := none, host := Std.Http.URI.Host.name \"proxy.example.com\", port := Std.Http.URI.Port.value 3128 }"),
    ("127.0.0.1:8080", "127.0.0.1:8080",
      "Std.Http.RequestTarget.authorityForm { userInfo := none, host := Std.Http.URI.Host.ipv4 127.0.0.1, port := Std.Http.URI.Port.value 8080 }"),
    ("1example.com:8080", "1example.com:8080",
      "Std.Http.RequestTarget.authorityForm { userInfo := none, host := Std.Http.URI.Host.name \"1example.com\", port := Std.Http.URI.Port.value 8080 }"),
    ("http://1example.com/path", "http://1example.com/path",
      "Std.Http.RequestTarget.absoluteForm { scheme := \"http\", authority := some { userInfo := none, host := Std.Http.URI.Host.name \"1example.com\", port := Std.Http.URI.Port.omitted }, path := { segments := #[\"path\"], absolute := true }, query := none, fragment := none }"),
    ("http://123abc.example.com/page", "http://123abc.example.com/page",
      "Std.Http.RequestTarget.absoluteForm { scheme := \"http\", authority := some { userInfo := none, host := Std.Http.URI.Host.name \"123abc.example.com\", port := Std.Http.URI.Port.omitted }, path := { segments := #[\"page\"], absolute := true }, query := none, fragment := none }")
  ] fun (_, s, want) => expectTarget s want

#eval checkCases "IPv4/IPv6 hosts at the very end of the input" #[
    ("192.168.0.1:80", "192.168.0.1:80",
      "Std.Http.RequestTarget.authorityForm { userInfo := none, host := Std.Http.URI.Host.ipv4 192.168.0.1, port := Std.Http.URI.Port.value 80 }"),
    ("http://[::1]/", "http://[::1]/",
      "Std.Http.RequestTarget.absoluteForm { scheme := \"http\", authority := some { userInfo := none, host := Std.Http.URI.Host.ipv6 ::1, port := Std.Http.URI.Port.omitted }, path := { segments := #[], absolute := true }, query := none, fragment := none }")
  ] fun (_, s, want) => expectTarget s want

#eval checkCases "A percent-encoded registered name is decoded (RFC 3986 §3.2.2, §6.2.2.2)" #[
    ("http://ex%41mple.com/", expectEq "host" ((hostOf "http://ex%41mple.com/").map toString)
      (some "example.com")),
    ("a percent-encoded address is that address", ensure (match hostOf "http://127.0.0.%31/" with
      | some (.ipv4 addr) => toString addr == "127.0.0.1"
      | _ => false) "http://127.0.0.%31/"),
    ("printing it and parsing it again gives the same host", ensure (match URI.parse? "http://%31%32%37.0.0.1/" with
      | some u => (URI.parse? (toString u)).bind (·.host?) == u.host?
      | none => false) "http://%31%32%37.0.0.1/")
  ] (·.2)

#eval checkCases "`_` is a reg-name character (#16079)" #[
    ("http://_svc.local/", expectEq "host" ((hostOf "http://_svc.local/").map toString) (some "_svc.local")),
    ("A dotted quad followed by `_svc` is a name", ensure (match hostOf "http://10.0.0.1_svc/" with
      | some (.name n) => toString n == "10.0.0.1_svc"
      | _ => false) "http://10.0.0.1_svc/")
  ] (·.2)

#eval checkCases "A fully qualified name ends in a single `.`, which adds no label" #[
    ("example.com.", ensure (URI.DomainName.ofString? "example.com.").isSome "example.com."),
    ("http://example.com./", expectEq "host" ((hostOf "http://example.com./").map toString)
      (some "example.com.")),
    ("example.com..", ensure (URI.DomainName.ofString? "example.com..").isNone "example.com..")
  ] (·.2)

private inductive HostKind where
  | notAHost
  | name
  | ipv4
  deriving BEq

/--
`parsed`: what `URI.parse?` (and, for `notAHost`, `DomainName.ofString?`) make of `host`;
`built`: what `Builder.setHost?` makes of it.
-/
private def expectHost (host : String) (parsed built : Option HostKind) : IO Unit := do
  match parsed with
  | some .notAHost =>
    if let some u := URI.parse? s!"http://{host}/" then
      throw <| IO.userError s!"http://{host}/ parsed with host {repr u.host?}"
    if (URI.DomainName.ofString? host).isSome then
      throw <| IO.userError s!"{host} is accepted as a domain name"
  | some .name =>
    unless hostOf s!"http://{host}/" matches some (.name _) do
      throw <| IO.userError s!"http://{host}/ does not parse with a domain name host"
  | some .ipv4 | none => pure ()
  match built with
  | some .notAHost => ensure (URI.Builder.empty.setHost? host).isNone s!"setHost? {host} was accepted"
  | some .name => ensure (match (URI.Builder.empty.setHost? host).bind (·.build.host?) with
      | some (.name n) => toString n == host
      | _ => false) s!"setHost? {host} is not a name"
  | some .ipv4 => ensure (match URI.Builder.empty.setScheme! "http" |>.setHost? host with
      | some b =>
        let u := b.build
        toString u == s!"http://{host}/" && u.host? == (URI.parse! s!"http://{host}/").host?
      | none => false) s!"setHost? {host} is not that address"
  | none => pure ()

-- The system resolver reads a name whose last label is a number as an IPv4 address in shorthand
-- (`127.1` is `127.0.0.1`), so such a name is not a domain name.
#eval checkCases "A name whose last label is a number is not a domain name" #[
    ("127.1", "127.1", some .notAHost, some .notAHost),
    ("2130706433", "2130706433", some .notAHost, none),
    ("0x7f.0.0.1", "0x7f.0.0.1", some .notAHost, none),
    ("1.2.3", "1.2.3", some .notAHost, none),
    ("example.0x1F", "example.0x1F", some .notAHost, none),
    ("127.1.", "127.1.", some .notAHost, none),
    ("1.example", "1.example", some .name, none),
    ("example.com1", "example.com1", some .name, none),
    ("a.b1c", "a.b1c", some .name, none),
    ("0x1g", "0x1g", some .name, none),
    ("setHost? takes a dotted-quad IPv4 address", "127.0.0.1", none, some .ipv4),
    ("setHost? 1.2.3.4.5", "1.2.3.4.5", none, some .notAHost),
    ("setHost? localhost", "localhost", none, some .name)
  ] fun (_, host, parsed, built) => expectHost host parsed built

-- A request target and a `Host` header take the RFC 3986 `host` (RFC 9110 §7.2, RFC 9112 §3.2), so a
-- percent-encoded name is decoded there as in any URI or reference.
#eval checkCases "Percent-encoded hosts in request targets and `Host`" #[
    ("absolute-form", expectPrints "http://ex%41mple.com/x" "http://example.com/x"),
    ("authority-form", expectPrints "ex%41mple.com:443" "example.com:443"),
    ("Host header", ensure (match hostHeader? "ex%41mple.com:8080" with
      | some (host, port) => toString host == "example.com" && port == .value 8080
      | none => false) "parseHostHeader ex%41mple.com:8080"),
    ("Decoding does not let through what the name itself could not hold: %2F",
      expectRejected "http://exa%2Fmple.com/x"),
    ("Decoding does not let through what the name itself could not hold: %00",
      ensure (hostHeader? "exa%00mple.com").isNone "parseHostHeader exa%00mple.com"),
    ("reference", ensure (match URIReference.parse? "//ex%41mple.com/x" with
      | some (.relative r) => r.authority.map (toString ·.host) == some "example.com"
      | _ => false) "//ex%41mple.com/x")
  ] (·.2)

private def longLabels : String := repeatStr "a" 63

private def name253 : String :=
  ".".intercalate [repeatStr "a" 63, repeatStr "b" 63, repeatStr "c" 63, repeatStr "d" 61]

#eval checkCases "Host-name length (RFC 1035 §2.3.4)" #[
    ("Domain names longer than 255 characters are rejected: DomainName.ofString?",
      ensure (URI.DomainName.ofString? s!"{longLabels}.{longLabels}.{longLabels}.{longLabels}.").isNone
        "256-character DomainName accepted"),
    ("Domain names longer than 255 characters are rejected: Builder.setHost?",
      ensure (URI.Builder.empty.setHost? s!"{longLabels}.{longLabels}.{longLabels}.{longLabels}.").isNone
        "256-character setHost? accepted"),
    ("URI with a 253-character host", ensure (URI.parse? s!"http://{name253}/").isSome
      "URI with a 253-character host was rejected"),
    ("Host of 253 characters", ensure (Header.Host.parse (.ofString! name253)).isSome
      "Host of 253 characters was rejected"),
    ("DomainName.ofString? of 253 characters", ensure (URI.DomainName.ofString? name253).isSome
      "DomainName.ofString? rejected 253 characters"),
    ("URI with a 254-character host ending in the root `.`", ensure (URI.parse? s!"http://{name253}./").isSome
      "URI with a 254-character host was rejected"),
    ("Host of 254 characters ending in the root `.`", ensure (Header.Host.parse (.ofString! (name253 ++ "."))).isSome
      "Host of 254 characters was rejected"),
    ("DomainName.ofString? of 254 characters ending in the root `.`",
      ensure (URI.DomainName.ofString? (name253 ++ ".")).isSome "DomainName.ofString? rejected 254 characters"),
    ("Control: 254 characters without the dot are too long", ensure (URI.parse? s!"http://e{name253}/").isNone
      "URI with a 254-character host was accepted")
  ] (·.2)


#eval checkCases "IP literals that parse are IPv6 addresses, printed in lowercase (RFC 3986 §3.2.2)" #[
    "[::ffff:192.168.0.1]", "[::ffff:c0a8:1]", "[1:2:3:4:5:6:7:8]", "[::12.34.56.78]",
    "[dead:beef:cafe:5417:affe:8FA3:deaf:feed]"
  ] fun lit => match hostOf s!"http://{lit}/" with
    | some h@(.ipv6 _) => ensure (toString h == (toString h).toLower) s!"{lit} printed as {toString h}"
    | other => throw <| IO.userError s!"{lit} gave host {reprLine other}"

#eval checkCases "Malformed IP literals and brackets are rejected (RFC 3986 §3.2.2)" #[
    "[::ffff:192.168.0.1000]", "[1:2:3:4:5:6:7:8:9]", "[1::1::1]", "[0439:23af::2309::fae7:1234]", "[1:2:3:]",
    "[192.168.0.1]", "[test.com]", "[important.com:8000]", "[not-an-ip]",
    "[::1]a", "[::1]%23", "fe80::1]", "::12.34.56.78]", "example.com[::1]", ".[::1]", "]v6a.ip[", "[::1/foo/",
    "1:2:3:4:5:6:7:8"
  ] fun host => ensure (URI.parse? s!"http://{host}/").isNone s!"http://{host}/ parsed"

/-! ## URI references (RFC 3986 §3.2, §4.2) -/

#eval checkCases "URI references" #[
    ("`file:///path` (empty authority) is an absolute URI", ensure (match URIReference.parse? "file:///etc/passwd" with
      | some (.absolute af) => af.scheme.val == "file" && af.authority.isNone
      | _ => false) "file:///etc/passwd"),
    ("//a:b/x: an authority that does not parse is never read as a path",
      ensure (URIReference.parse? "//a:b/x").isNone "//a:b/x"),
    ("//a:1/x", ensure (URIReference.parse? "//a:1/x").isSome "//a:1/x"),
    ("1:b: the first segment of a relative path cannot contain `:`",
      ensure (URIReference.parse? "1:b").isNone "1:b"),
    ("./1:b", ensure (URIReference.parse? "./1:b").isSome "./1:b"),
    ("a/1:b", ensure (URIReference.parse? "a/1:b").isSome "a/1:b")
  ] (·.2)


#eval checkCases "Absolute URIs with a rootless or empty path round-trip (RFC 3986 §3)" #[
    "mailto:webmaster@example.org", "magnet:?xt=urn:btih:c12fe1&dn", "mailto:?subject=hi",
    "sip:alice@atlanta.com;maddr=239.255.255.1;ttl=15", "tel:+31-641044153", "path:80"
  ] fun s => match URIReference.parse? s with
    | some r@(.absolute u) => do
      ensure u.authority.isNone s!"{s} has an authority"
      expectEq "printed" (toString r) s
    | other => throw <| IO.userError s!"{s} gave {reprLine (other.map toString)}"

#eval checkCases "Any scheme takes an authority" #[
    "s3://foo.com/stuff", "x-newscheme://foo.com/stuff?query#fragment"
  ] fun s => match URIReference.parse? s with
    | some r@(.absolute u) => do
      ensure (u.authority.map (toString ·.host) == some "foo.com") s!"{s}: authority"
      expectEq "printed" (toString r) s
    | other => throw <| IO.userError s!"{s} gave {reprLine (other.map toString)}"

#eval checkCases "`_` is not a scheme character (RFC 3986 §3.1, §4.2)" #[
    ("cache_object://foo", ensure (URIReference.parse? "cache_object://foo").isNone "cache_object://foo parsed"),
    ("cache_object:foo", ensure (URIReference.parse? "cache_object:foo").isNone "cache_object:foo parsed"),
    ("cache_object/:foo/bar is a relative reference",
      ensure (URIReference.parse? "cache_object/:foo/bar" matches some (.relative _)) "cache_object/:foo/bar")
  ] (·.2)

#eval checkCases "A fragment may hold `@ : / ?` (RFC 3986 §3.5)" #[
    ("//abc#@frag:80", ensure (match URIReference.parse? "//abc#@frag:80" with
      | some (.relative r) =>
        r.fragment == some "@frag:80" && r.authority.map (toString ·.host) == some "abc" &&
          r.authority.map (·.port) == some .omitted
      | _ => false) "//abc#@frag:80")
  ] (·.2)

/-! ## Limits -/

#eval checkCases "Limits" #[
    ("maxPathSegments should apply to trailing empty segments as well", ensure
      (((parseURI { maxPathSegments := 1 } <* Std.Internal.Parsec.eof).run
        "http://example.com/a/".toUTF8).toOption.isNone) "http://example.com/a/ parsed"),
    ("257-byte segment", ensure (URI.parse? ("http://example.com/" ++ repeatStr "a" 257)).isSome
      "URI.parse? rejected a URI with a 257-byte segment"),
    ("129 segments", ensure (URI.parse? ("http://example.com" ++ repeatStr "/a" 129)).isSome
      "URI.parse? rejected a URI with 129 segments"),
    ("101 query parameters", ensure
      (URI.parse? ("http://example.com/?" ++ "&".intercalate (List.replicate 101 "a=1"))).isSome
      "URI.parse? rejected a URI with 101 query parameters"),
    ("1100-byte fragment", ensure (URI.parse? ("http://example.com/#" ++ repeatStr "f" 1100)).isSome
      "URI.parse? rejected a URI with a 1100-byte fragment"),
    ("16-character scheme", ensure (URI.parse? "chrome-extension://abcdef/x").isSome
      "URI.parse? rejected a URI with a 16-character scheme")
  ] (·.2)
