module

import Std.Http.Test.Helpers
import Std.Http.Test.Machine

/-!
# HTTP/1.1 request heads

What a server accepts as a request head: the request line, leading empty lines, the method, the
version, the request-target form, `Host`, field lines, and heads that are not HTTP at all. Each rule
has its machine table (`MachineTester`) next to its `serveConnection` table, which pins the exact
response. RFC 9112 §2.2, §2.3, §3, §5; RFC 9110 §5.5, §7.2, §9.1, §9.3.6.
-/

open Std Http
open Std.Http.Protocol.H1
open Std.Http.Internal.Test

/-- Serves `raw` with `okHandler`; with `closeInput` the client sends EOF after it. -/
private def expectServer (raw : String) (want : Want) (closeInput : Bool := false) : IO Unit :=
  checkHandler raw okHandler want (closeInput := closeInput)

/-! ## Request-line syntax (RFC 9112 §3) -/

#eval checkCases "RFC 9112 §3: request-line parse failures" #[
    ("missing version → 400", "GET /\x0d\nHost: example.com\x0d\n\x0d\n", Want.exact r400, false),
    ("missing URI (double space) → 400", "GET  HTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n", .exact r400, false),
    ("extra spaces in request-line → 400",
      "GET  /  HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n", .exact r400, false),
    ("whitespace-only request-line → 400", "   \x0d\n\x0d\n", .exact r400, false),
    ("no spaces in request-line → 400", "GETHTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n", .exact r400, false),
    ("garbage after request-line version → 400",
      "GET / HTTP/1.1 xxxxxx\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n", .exact r400, false),
    ("empty connection → silent close", "", .exact "", true)
  ] fun (_, raw, want, closeInput) => expectServer raw want closeInput

#eval checkCases "RFC 9112 §2.2, §3: early invalid bytes" #[
    ("NUL byte → 400", "\x00"),
    ("SP byte → 400", "\x20"),
    ("TLS client-hello prefix → 400", "\x16\x03\x01\x00\xa5")
  ] fun (_, raw) => expectServer raw (.exact r400) (closeInput := true)


#eval checkCases "Request-line shapes that are not a request line" #[
    (" / HTTP/1.1", " / HTTP/1.1\x0d\nHost: a\x0d\n\x0d\n"),
    ("  HTTP/1.1", "  HTTP/1.1\x0d\nHost: a\x0d\n\x0d\n"),
    (" GET / HTTP/1.1", " GET / HTTP/1.1\x0d\nHost: a\x0d\n\x0d\n"),
    ("GET /spaced out HTTP/1.1", "GET /spaced out HTTP/1.1\x0d\nHost: a\x0d\n\x0d\n"),
    ("a token with no SP gets 400, not 501", "gibberish\x0d\n\x0d\n"),
    ("CR as a separator", "GET\x0d/\x0dHTTP/1.1\x0d\nHost: a\x0d\n\x0d\n"),
    ("LF inside the request line", "GET\n/ HTTP/1.1\x0d\nHost: a\x0d\n\x0d\n"),
    ("CR CR LF after the version", "GET / HTTP/1.1\x0d\x0d\nHost: a\x0d\n\x0d\n")
  ] fun (_, raw) => checkHandler raw okHandler (.exact r400) (closeInput := true)

-- RFC 9112 §3: an invalid request line SHOULD get 400, without waiting for more input.
#eval checkCases "A request line with no version fails at once" #[
    ("GET / then an empty line", "GET /\r\n\r\n"),
    ("GET /x then a field", "GET /x\r\nHost:a\r\n\r\n")
  ] fun (label, raw) => MachineTester.receiving label |>.feed raw |>.step |>.assertFailedWith .badMessage |>.run

-- RFC 9112 §8: an incomplete request is never handed to the handler.
#eval checkCases "Every proper prefix of a request head, then EOF" #[
    ("prefixes of a GET head", do
      let head := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n"
      for n in [1:head.length] do
        let (r, seen) ← serveRecording (String.ofList (head.toList.take n)) (closeInput := true)
        ensure seen.isEmpty s!"prefix of {n} bytes: the handler ran"
        ensure (String.fromUTF8! r == r400) s!"prefix of {n} bytes: got {(String.fromUTF8! r).quote}"),
    ("zero bytes, then EOF", do
      let (r, seen) ← serveRecording "" (closeInput := true)
      ensure (r.isEmpty && seen.isEmpty) "expected a silent close")
  ] (·.2)

/-! ## Leading empty lines (RFC 9112 §2.2) -/

#eval checkCases "RFC 9112 §2.2: leading CRLF before request-line: machine" #[
    ("§2.2: leading CRLF ignored", MachineTester.receiving "§2.2: leading CRLF ignored" (config := { maxLeadingEmptyLines := 8 })
      |>.feed "\r\n\r\nGET / HTTP/1.1\r\nHost: example.com\r\n\r\n"
      |>.step |>.assertNoError |>.assertHasEndHeaders |>.run),
    ("§2.2: maximum leading CRLFs", MachineTester.receiving "§2.2: maximum leading CRLFs" (config := { maxLeadingEmptyLines := 2 })
      |>.feed "\r\n\r\n\r\nGET / HTTP/1.1\r\nHost: example.com\r\n\r\n"
      |>.step |>.assertFailedWith .badMessage |>.run)
  ] (·.2)

#eval checkCases "RFC 9112 §2.2: empty lines before a request and before EOF: server" #[
    ("CRLF after a body, then EOF", "POST / HTTP/1.1\x0d\nHost: a\x0d\nContent-Length: 2\x0d\n\x0d\nhi\x0d\n",
      Want.all [.status "HTTP/1.1 200", .responses 1], true),
    ("only empty lines, then EOF", "\x0d\n\x0d\n", .exact "", true),
    ("single leading CRLF accepted",
      "\x0d\nGET / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n", .exact okResponse, false)
  ] fun (_, raw, want, closeInput) => expectServer raw want closeInput


#eval checkCases "Empty lines between pipelined requests" #[
    ("CRLF CRLF after a body, then a GET", do
      let (r, seen) ← serveRecording ("POST / HTTP/1.1\x0d\nHost: a\x0d\nContent-Length: 3\x0d\n\x0d\nABC" ++
        "\x0d\n\x0d\nGET / HTTP/1.1\x0d\nHost: a\x0d\nConnection: close\x0d\n\x0d\n") (closeInput := true)
      (Want.responses 2).check r
      ensure (seen.size == 2) s!"expected 2 handler calls, got {seen.size}")
  ] (·.2)

/-! ## Method (RFC 9110 §9.1, RFC 9112 §3) -/

-- A well-formed method the server does not recognize, or one longer than any it implements, is
-- answered with 501. Methods are case-sensitive.
#eval checkCases "RFC 9110 §9.1: unrecognized methods: machine" #[
    ("LEAN", "LEAN"), ("GETX", "GETX"), ("get", "get"), ("X-CUSTOM", "X-CUSTOM"), ("UPDATEX", "UPDATEX"),
    ("a 65-byte token", String.ofList (List.replicate 65 'G'))
  ] fun (label, method) =>
    MachineTester.receiving s!"§3: unrecognized method {label} → unsupportedMethod"
      |>.feed s!"{method} / HTTP/1.1\r\nHost: example.com\r\n\r\n"
      |>.step |>.assertFailedWith .unsupportedMethod
      |>.step |>.assertOutputStartsWith "HTTP/1.1 501 Not Implemented\r\n" "expected 501" |>.run

-- A method that is not a token makes the request line malformed.
#eval checkCases "RFC 9112 §3: non-token methods: machine" #[
    "G@T / HTTP/1.1", "GÉT / HTTP/1.1", "GET\t/ HTTP/1.1", "GETHTTP/1.1"
  ] fun line =>
    MachineTester.receiving s!"§3: {line.quote} → badMessage"
      |>.feed s!"{line}\r\nHost: example.com\r\n\r\n"
      |>.step |>.assertFailedWith .badMessage |>.run

#eval checkCases "RFC 9110 §9: method validation: server" #[
    ("unknown method FOOBAR → 501", "FOOBAR / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n", r501),
    ("lowercase method → 501", "get / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n", r501),
    ("non-ASCII method → 400", "GÉT / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n", r400),
    ("very long unrecognized method → 501",
      s!"{String.ofList (List.replicate 100 'G')} / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n", r501),
    ("token method with hyphen (X-CUSTOM) → 501",
      "X-CUSTOM / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n", r501),
    ("method that starts with a known one (GETX) → 501",
      "GETX / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n", r501)
  ] fun (_, raw, want) => expectServer raw (.exact want)

/-! ## Version (RFC 9112 §2.3, RFC 9110 §2.5) -/

#eval checkCases "RFC 9112 §2.3: HTTP version: machine" #[
    ("§2: HTTP/2.0 → unsupportedVersion", MachineTester.receiving "§2: HTTP/2.0 → unsupportedVersion"
      |>.feed "GET / HTTP/2.0\r\nHost: example.com\r\n\r\n"
      |>.step |>.assertFailedWith .unsupportedVersion |>.run),
    ("§2: HTTP/0.9 → unsupportedVersion", MachineTester.receiving "§2: HTTP/0.9 → unsupportedVersion"
      |>.feed "GET / HTTP/0.9\r\nHost: example.com\r\n\r\n"
      |>.step |>.assertFailedWith .unsupportedVersion |>.run),
    ("§2: HTTP/3.0 → unsupportedVersion", MachineTester.receiving "§2: HTTP/3.0 → unsupportedVersion"
      |>.feed "GET / HTTP/3.0\r\nHost: example.com\r\n\r\n"
      |>.step |>.assertFailedWith .unsupportedVersion |>.run)
  ] (·.2)

-- RFC 9110 §6.2: a higher minor version is processed as the highest minor version the recipient
-- implements.
#eval checkCases "RFC 9110 §6.2: a higher minor version is read as HTTP/1.1: machine" #[
    "HTTP/1.2", "HTTP/1.9"
  ] fun version =>
    MachineTester.receiving s!"§2: {version} request is read as HTTP/1.1"
      |>.feed s!"GET / {version}\r\nHost: example.com\r\n\r\n"
      |>.step |>.assertNoError |>.assertHasEndHeaders |>.assertKeepAlive
      |>.onEndHeaders (fun t head =>
        if head.version != .v11 then t.addError s!"expected HTTP/1.1, got {repr head.version}" else t)
      |>.send { status := .ok } |>.setKnownSize (.fixed 0) |>.userClosedBody |>.step
      |>.assertOutputStartsWith "HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n" "expected an HTTP/1.1 response"
      |>.assertKeepAlive |>.run

#eval checkCases "RFC 9112 §2.3, RFC 9110 §2.5: HTTP version: server" #[
    ("HTTP/2.0 → 505", "GET / HTTP/2.0\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
  ] fun (_, raw) => expectServer raw (.exact r505)


#eval checkCases "Version table" #[
    ("HTTP/0.0 → 505", "HTTP/0.0", r505),
    ("HTTP/3.14", "HTTP/3.14", r400), ("HTTP/12.3", "HTTP/12.3", r400), ("HTTP/1.+1", "HTTP/1.+1", r400),
    ("HTTP/1,1", "HTTP/1,1", r400), ("HTTP/1", "HTTP/1", r400), ("http/1.1", "http/1.1", r400),
    ("HTTP/1.1/", "HTTP/1.1/", r400), ("FUBAR", "FUBAR", r400), ("HTTP/9.9.9", "HTTP/9.9.9", r400),
    ("HTTP/-9_9_9.+9_9_9", "HTTP/-9_9_9.+9_9_9", r400), ("HTTP/909876543210.0", "HTTP/909876543210.0", r400),
    ("HTTP/1.909876543210", "HTTP/1.909876543210", r400)
  ] fun (_, v, want) => checkHandler s!"GET / {v}\x0d\nHost: a\x0d\nConnection: close\x0d\n\x0d\n" okHandler (.exact want)

#eval checkCases "A malformed version fails before its CRLF" #[
    ("GET / HTTP/1!", MachineTester.receiving "GET / HTTP/1!" |>.feed "GET / HTTP/1!" |>.step
      |>.assertFailedWith .badMessage |>.run)
  ] (·.2)

/-! ## Request-target form (RFC 9112 §3.2) -/

#eval checkCases "RFC 9112 §3.2: request-target form: machine" #[
    ("§3.2.1: origin-form path preserved", MachineTester.receiving "§3.2.1: origin-form path preserved"
      |>.feed "GET /api/v1/users?active=true HTTP/1.1\r\nHost: api.example.com\r\n\r\n"
      |>.step |>.assertNoError
      |>.onEndHeaders (fun t head =>
        let path := toString head.uri.path
        if path != "/api/v1/users" then t.addError s!"expected path /api/v1/users, got {path}"
        else t)
      |>.run),
    ("§3.2: non-OPTIONS asterisk-form → badMessage", MachineTester.receiving "§3.2: non-OPTIONS asterisk-form → badMessage"
      |>.feed "GET * HTTP/1.1\r\nHost: example.com\r\n\r\n"
      |>.step |>.assertFailedWith .badMessage |>.run),
    ("§3.2: non-CONNECT authority-form → badMessage", MachineTester.receiving "§3.2: non-CONNECT authority-form → badMessage"
      |>.feed "GET example.com:80 HTTP/1.1\r\nHost: example.com\r\n\r\n"
      |>.step |>.assertFailedWith .badMessage |>.run),
    ("§3.3: absolute-form with explicit :80", MachineTester.receiving "§3.3: absolute-form with explicit :80"
      |>.feed "GET http://example.com:80/path HTTP/1.1\r\nHost: example.com\r\n\r\n"
      |>.step |>.assertNoError |>.assertHasEndHeaders |>.run)
  ] (·.2)

#eval checkCases "RFC 9112 §3.2: request target forms: server" #[
    ("GET authority-form → 400", "GET example.com:443 HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n", r400),
    ("GET asterisk-form → 400", "GET * HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n", r400),
    ("OPTIONS * accepted", "OPTIONS * HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n", okResponse),
    ("absolute-form URI accepted", "GET http://example.com/path HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n", okResponse)
  ] fun (_, raw, want) => expectServer raw (.exact want)


private def pathAndAuthority : TestHandler := fun req =>
  Response.ok |>.text s!"{toString req.line.uri}|{req.line.uri.authority?.isNone}"

-- RFC 9112 §3.2.1: an origin-form target may begin with `//`; it is a path, never an authority.
#eval checkCases "Origin-form targets that begin with `//`" #[
    "//user@host/is/actually/a/path/", "//", "///////", "//@", "//://///"
  ] fun target =>
    checkHandler s!"GET {target} HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n" pathAndAuthority
      (.body s!"{target}|true")

#eval checkCases "Targets that fit no form" #[
    "../../../../etc/passwd", "sd", "test?test", "x@x.com", "?x", "example.com/", "1234567890",
    ":a@example.net", "http:www.example.com/", "/p#f", "http://h/p#f"
  ] fun target =>
    checkHandler s!"GET {target} HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n" okHandler (.exact r400)

#eval checkCases "Accepted target forms" #[
    ("the scheme is case-insensitive", "GET HTTP://example.com/ HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"),
    ("OPTIONS * over HTTP/1.0 without Host", "OPTIONS * HTTP/1.0\x0d\n\x0d\n"),
    ("absolute-form of another scheme reaches the handler", "GET urn:isbn:0451450523 HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
  ] fun (_, raw) => checkHandler raw okHandler (.status "HTTP/1.1 200")

private def targetRequest (target : ByteArray) : ByteArray :=
  "GET ".toUTF8 ++ target ++ " HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8

-- RFC 3986 §2: a byte outside the URI grammar must be percent-encoded.
#eval checkCases "Raw bytes in the target" #[
    ("0x80", ByteArray.mk #[0x2F, 0x61, 0x80], Want.exact r400), ("0xEE", ByteArray.mk #[0x2F, 0x61, 0xEE], .exact r400),
    ("HTAB", "/a\tb".toUTF8, .exact r400), ("DEL", "/a\x7fb".toUTF8, .exact r400), ("NUL", "/a\x00b".toUTF8, .exact r400),
    ("raw UTF-8 in the path", "/caf\xc3\xa9".toUTF8, .exact r400), ("raw UTF-8 in the query", "/?q=caf\xc3\xa9".toUTF8, .exact r400),
    ("an invalid UTF-8 byte", ByteArray.mk #[0x2F, 0xC3], .exact r400),
    ("`", "/a`b".toUTF8, .exact r400), ("{", "/a{b".toUTF8, .exact r400), ("}", "/a}b".toUTF8, .exact r400), ("^", "/a^b".toUTF8, .exact r400),
    ("|", "/a|b".toUTF8, .exact r400), ("\\", "/a\\b".toUTF8, .exact r400), ("[", "/a[b".toUTF8, .exact r400), ("]", "/a]b".toUTF8, .exact r400),
    ("\"", "/a\"b".toUTF8, .exact r400),
    ("percent-encoded forms", "/%80%EE%09%7F%00%C3%A9%60%7B%7D%5E%7C%5C%5B%5D%22?q=caf%C3%A9".toUTF8, .status "HTTP/1.1 200")
  ] fun (_, target, want) => do want.check (← serveBytes (targetRequest target) okHandler)

-- RFC 9110 §4.2.4: a recipient SHOULD treat userinfo in a request-target as an error.
#eval checkCases "absolute-form with userinfo" #[
    ("http://user:pass@example.com/", "GET http://user:pass@example.com/ HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
  ] fun (_, raw) => checkHandler raw okHandler (.exact r400)

#eval checkCases "CONNECT targets that are not an authority" #[
    ("origin-form", "CONNECT /_goRPC_ HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n"),
    ("a bad authority", "CONNECT []%20%48%54%54%50 HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
  ] fun (_, raw) => checkHandler raw okHandler (.exact r400)

/-! ## Host (RFC 9112 §3.2, RFC 9110 §7.2) -/

#eval checkCases "RFC 9112 §3.2: Host: machine" #[
    ("§3.2: HTTP/1.1 missing Host → badMessage", MachineTester.receiving "§3.2: HTTP/1.1 missing Host → badMessage"
      |>.feed "GET / HTTP/1.1\r\n\r\n"
      |>.step |>.assertFailedWith .badMessage |>.run),
    ("§3.2: HTTP/1.1 duplicate Host → badMessage", MachineTester.receiving "§3.2: HTTP/1.1 duplicate Host → badMessage"
      |>.feed "GET / HTTP/1.1\r\nHost: a.com\r\nHost: b.com\r\n\r\n"
      |>.step |>.assertFailedWith .badMessage |>.run),
    ("§7.2: HTTP/1.1 empty Host valid for origin-form", MachineTester.receiving "§7.2: HTTP/1.1 empty Host valid for origin-form"
      |>.feed "GET / HTTP/1.1\r\nHost: \r\n\r\n"
      |>.step |>.assertNoError |>.assertHasEndHeaders |>.run),
    ("RFC 9112 §3.2: HTTP/1.0 without Host → valid", MachineTester.receiving "RFC 9112 §3.2: HTTP/1.0 without Host → valid"
      |>.feed "GET / HTTP/1.0\r\n\r\n"
      |>.step |>.assertNoError |>.assertHasEndHeaders |>.run),
    ("RFC 9112 §3.2: HTTP/1.0 single Host → valid", MachineTester.receiving "RFC 9112 §3.2: HTTP/1.0 single Host → valid"
      |>.feed "GET / HTTP/1.0\r\nHost: example.com\r\n\r\n"
      |>.step |>.assertNoError |>.assertHasEndHeaders |>.run),
    ("RFC 9112 §3.2: HTTP/1.0 duplicate Host → badMessage", MachineTester.receiving "RFC 9112 §3.2: HTTP/1.0 duplicate Host → badMessage"
      |>.feed "GET / HTTP/1.0\r\nHost: a.com\r\nHost: b.com\r\n\r\n"
      |>.step |>.assertFailedWith .badMessage |>.run),
    -- RFC 9110 §7.2: `Host` is an RFC 3986 `host`, which may be percent-encoded. The field reaches
    -- the handler as sent.
    ("§3.2: percent-encoded Host accepted", MachineTester.receiving "§3.2: percent-encoded Host accepted"
      |>.feed "GET / HTTP/1.1\r\nHost: ex%41mple.com\r\n\r\n"
      |>.step |>.assertNoError
      |>.onEndHeaders (fun t head =>
        match head.headers.get? .host with
        | some v => if v.value == "ex%41mple.com" then t else t.addError s!"expected Host=ex%41mple.com, got {v.value.quote}"
        | none => t.addError "missing Host header")
      |>.run),
    ("§3.3: percent-encoded absolute-form host decoded", MachineTester.receiving "§3.3: percent-encoded absolute-form host decoded"
      |>.feed "GET http://ex%41mple.com/ HTTP/1.1\r\nHost: example.com\r\n\r\n"
      |>.step |>.assertNoError
      |>.onEndHeaders (fun t head =>
        match head.uri.authority? with
        | some a => if toString a == "example.com" then t else t.addError s!"expected URI authority=example.com, got {toString a}"
        | none => t.addError "missing URI authority")
      |>.run),
    ("§3.2: Host with a percent-encoded `/` → badMessage", MachineTester.receiving "§3.2: Host with a percent-encoded `/` → badMessage"
      |>.feed "GET / HTTP/1.1\r\nHost: exa%2Fmple.com\r\n\r\n"
      |>.step |>.assertFailedWith .badMessage |>.run),
    -- RFC 9112 §3.2.2: Host is left as-is; the authority is available through the URI.
    ("§3.2: absolute-form Host preserved, authority in URI", MachineTester.receiving "§3.2: absolute-form Host preserved, authority in URI"
      |>.feed "GET http://example.com:80/path HTTP/1.1\r\nHost: random.com\r\n\r\n"
      |>.step |>.assertNoError
      |>.onEndHeaders (fun t head =>
        let t := match head.headers.get? .host with
          | some v => if v.value == "random.com" then t else t.addError s!"expected Host=random.com, got {v.value.quote}"
          | none => t.addError "missing Host header"
        match head.uri.authority? with
          | some a => if toString a == "example.com:80" then t else t.addError s!"expected URI authority=example.com:80, got {toString a}"
          | none => t.addError "missing URI authority")
      |>.run)
  ] (·.2)

#eval checkCases "RFC 9112 §3.2: Host header: server" #[
    ("missing Host header → 400", "GET / HTTP/1.1\x0d\nConnection: close\x0d\n\x0d\n", Want.exact r400),
    ("empty Host allowed for origin-form", "GET / HTTP/1.1\x0d\nHost: \x0d\nConnection: close\x0d\n\x0d\n", .exact okResponse),
    ("multiple Host headers → 400",
      "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nHost: other.com\x0d\nConnection: close\x0d\n\x0d\n", .exact r400),
    ("Host: example.com:000080",
      "GET / HTTP/1.1\x0d\nHost: example.com:000080\x0d\nConnection: close\x0d\n\x0d\n", .status "HTTP/1.1 200"),
    ("CONNECT with an empty port",
      "CONNECT example.com: HTTP/1.1\x0d\nHost: example.com:\x0d\nConnection: close\x0d\n\x0d\n", .status "HTTP/1.1 400")
  ] fun (_, raw, want) => expectServer raw want

-- RFC 9112 §3.2.2: for an absolute-form target, the server uses the target's authority, not `Host`.
#eval checkCases "absolute-form: URI authority takes precedence over Host" #[
    ("absolute-form: URI authority takes precedence over Host",
      "GET http://good.example/path HTTP/1.1\x0d\nHost: other.example\x0d\nConnection: close\x0d\n\x0d\n")
  ] fun (_, raw) =>
    checkHandler raw (show TestHandler from fun req => Response.ok |>.text ((req.line.uri.authority?.map toString).getD "<none>"))
      (.body "good.example")

-- A 2xx to CONNECT starts a tunnel, so it has no framing fields or content (RFC 9110 §9.3.6).
#eval checkCases "CONNECT authority vs Host: server" #[
    ("CONNECT authority-form accepted",
      "CONNECT example.com:443 HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n",
      "HTTP/1.1 200 OK\x0d\nContent-Type: text/plain; charset=utf-8\x0d\nServer: LeanHTTP/1.1\x0d\nConnection: close\x0d\n\x0d\n"),
    ("CONNECT authority-form port mismatch → 400",
      "CONNECT example.com:444 HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n", r400)
  ] fun (_, raw, want) => expectServer raw (.exact want)


private def hostRequest (version : String) (host : ByteArray) : ByteArray :=
  s!"GET / {version}\x0d\nHost: ".toUTF8 ++ host ++ "\x0d\nConnection: close\x0d\n\x0d\n".toUTF8

-- RFC 9110 §7.2: `Host` is `uri-host [ ":" port ]`.
#eval checkCases "Host values" #[
    ("1.2.3.4", "1.2.3.4".toUTF8, true), ("foo.com:80", "foo.com:80".toUTF8, true), ("foo-bar_baz.com", "foo-bar_baz.com".toUTF8, true),
    ("[::1]", "[::1]".toUTF8, true), ("[::1]:80", "[::1]:80".toUTF8, true), ("[::1]:8080", "[::1]:8080".toUTF8, true),
    ("[::ffff:12.34.56.78]", "[::ffff:12.34.56.78]".toUTF8, true), ("an empty port", "example.com:".toUTF8, true), ("empty", ByteArray.empty, true),
    ("::1", "::1".toUTF8, false), ("[::1", "[::1".toUTF8, false), ("::1]", "::1]".toUTF8, false), ("{", "{".toUTF8, false),
    ("}", "}".toUTF8, false), ("0x06", ByteArray.mk #[0x06], false), ("0xFF", ByteArray.mk #[0xFF], false),
    ("user@example.com", "user@example.com".toUTF8, false), ("example.com:abc", "example.com:abc".toUTF8, false),
    ("example.com:80:", "example.com:80:".toUTF8, false)
  ] fun (_, host, ok) => do
    (if ok then Want.status "HTTP/1.1 200" else .exact r400).check (← serveBytes (hostRequest "HTTP/1.1" host) okHandler)

#eval checkCases "Host presence" #[
    ("HTTP/1.0 with an invalid Host", hostRequest "HTTP/1.0" (ByteArray.mk #[0xFF])),
    ("CONNECT without Host", "CONNECT example.com:443 HTTP/1.1\x0d\nConnection: close\x0d\n\x0d\n".toUTF8),
    ("absolute-form without Host", "GET http://example.com/ HTTP/1.1\x0d\nConnection: close\x0d\n\x0d\n".toUTF8)
  ] fun (_, raw) => do (Want.exact r400).check (← serveBytes raw okHandler)

-- RFC 9110 §9.3.6's own example: a port-less `Host` matches a target port of 80.
#eval checkCases "CONNECT authority vs Host: port 80" #[
    ("CONNECT server.example.com:80 with Host server.example.com",
      "CONNECT server.example.com:80 HTTP/1.1\x0d\nHost: server.example.com\x0d\nConnection: close\x0d\n\x0d\n")
  ] fun (_, raw) => checkHandler raw okHandler
    (.exact "HTTP/1.1 200 OK\x0d\nContent-Type: text/plain; charset=utf-8\x0d\nServer: LeanHTTP/1.1\x0d\nConnection: close\x0d\n\x0d\n")

/-! ## Field lines (RFC 9112 §5, RFC 9110 §5.5) -/

#eval checkCases "RFC 9110 §6–§7: header handling: machine" #[
    ("§6.3: custom headers preserved", MachineTester.receiving "§6.3: custom headers preserved"
      |>.feed "GET / HTTP/1.1\r\nHost: example.com\r\nX-Custom: my-value\r\nAuthorization: Bearer tok\r\n\r\n"
      |>.step |>.assertNoError
      |>.onEndHeaders (fun t head =>
        let custom := (head.headers.get? (.ofString! "X-Custom")).map (·.value)
        let auth := (head.headers.get? .authorization).map (·.value)
        if custom != some "my-value" then t.addError s!"X-Custom mismatch: {repr custom}"
        else if auth != some "Bearer tok" then t.addError s!"Authorization mismatch: {repr auth}"
        else t)
      |>.run)
  ] (·.2)

#eval checkCases "RFC 9112 §5: header field syntax: server" #[
    ("header without colon → 400",
      "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nBadHeader value\x0d\nConnection: close\x0d\n\x0d\n", r400),
    ("leading whitespace (obs-fold) → 400",
      "GET / HTTP/1.1\x0d\nHost: example.com\x0d\n X-Bad: folded\x0d\nConnection: close\x0d\n\x0d\n", r400),
    ("space in header name → 400",
      "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nBad Header: value\x0d\nConnection: close\x0d\n\x0d\n", r400),
    ("bare LF line endings → 400", "GET / HTTP/1.1\nHost: example.com\nConnection: close\n\n", r400),
    ("tab in header value → accepted",
      "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nX-Tab: value\twith\ttabs\x0d\nConnection: close\x0d\n\x0d\n", okResponse),
    ("NUL in header name → 400",
      "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nX-Bad\x00Header: value\x0d\nConnection: close\x0d\n\x0d\n", r400),
    ("NUL in header value → 400",
      "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nX-Header: bad\x00value\x0d\nConnection: close\x0d\n\x0d\n", r400),
    ("control char (0x01) in header value → 400",
      "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nX-Header: bad\x01value\x0d\nConnection: close\x0d\n\x0d\n", r400)
  ] fun (_, raw, want) => expectServer raw (.exact want)

-- The name ends at the first `:`; later colons belong to the value.
#eval checkCases "additional colon in header value stays in value" #[
    ("additional colon in header value stays in value",
      "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nBad:Name: value\x0d\nConnection: close\x0d\n\x0d\n")
  ] fun (_, raw) =>
    checkHandler raw
      (show TestHandler from fun req =>
        Response.ok |>.text (((req.line.headers.get? (Header.Name.ofString! "Bad")).map (·.value)).getD "<none>"))
      (.body "Name: value")


-- RFC 9112 §5.1: no whitespace between a field name and its colon; RFC 9112 §2.2: a whitespace-led
-- line right after the request line is rejected.
#eval checkCases "Field-line syntax" #[
    ("Host : x", "GET / HTTP/1.1\x0d\nHost : example.com\x0d\nConnection: close\x0d\n\x0d\n"),
    ("Foo HTAB :", "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nFoo\t: x\x0d\nConnection: close\x0d\n\x0d\n"),
    ("Content-Length : 5", "POST / HTTP/1.1\x0d\nHost: example.com\x0d\nContent-Length : 5\x0d\nConnection: close\x0d\n\x0d\nhello"),
    ("an empty name", "GET / HTTP/1.1\x0d\nHost: example.com\x0d\n: value\x0d\nConnection: close\x0d\n\x0d\n"),
    ("a SP-led line after the request line", "GET / HTTP/1.1\x0d\n Host: example.com\x0d\nConnection: close\x0d\n\x0d\n"),
    ("a HTAB-led line after the request line", "GET / HTTP/1.1\x0d\n\tHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
  ] fun (_, raw) => checkHandler raw okHandler (.exact r400)

private def isTchar (b : UInt8) : Bool :=
  let c := Char.ofNat b.toNat
  c.isAlphanum && b < 128 || "!#$%&'*+-.^_`|~".contains c

-- RFC 9110 §5.1, §5.5, §5.6.2: a field name is a token; a field value is VCHAR, obs-text, SP and HTAB.
#eval checkCases "Every byte in a field name and in a field value" #[
    ("name Foo?Bar: foo", do
      for n in [0:256] do
        let b := n.toUInt8
        let raw := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nFoo".toUTF8.push b ++ "Bar: foo\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
        let ok := isTchar b || b == ':'.toUInt8
        try (if ok then Want.status "HTTP/1.1 200" else .exact r400).check (← serveBytes raw okHandler)
        catch e => throw <| IO.userError s!"byte {n}: {e}"),
    ("value Foo: foo?bar", do
      for n in [0:256] do
        let b := n.toUInt8
        let raw := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nFoo: foo".toUTF8.push b ++ "bar\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
        let ok := b == 0x20 || b == 0x09 || (0x21 ≤ b && b ≤ 0x7E) || 0x80 ≤ b
        try (if ok then Want.status "HTTP/1.1 200" else .exact r400).check (← serveBytes raw okHandler)
        catch e => throw <| IO.userError s!"byte {n}: {e}"),
    ("a name made only of tchar specials", checkHandler
      "GET / HTTP/1.1\x0d\nHost: example.com\x0d\n!#$%&'*+-.^_`|~: x\x0d\nConnection: close\x0d\n\x0d\n" okHandler (.status "HTTP/1.1 200"))
  ] (·.2)

private def fieldValues (name : String) : TestHandler := fun req =>
  Response.ok |>.text (match req.line.headers.getAll? (Header.Name.ofString! name) with
    | some vs => "|".intercalate (vs.map (·.value)).toList
    | none => "<none>")

-- RFC 9110 §5.5, §5.6.3: OWS around a value is not part of it; RFC 9110 §5.3: field lines with one
-- name are one field, in order.
#eval checkCases "What the handler sees of a field" #[
    ("b:1 SP HTAB", "b:1 \t", "b", "1"), ("X: HTAB SP v", "X:\t v", "X", "v"),
    ("trailing SP", "Foo: a a a a a ", "Foo", "a a a a a"), ("Foo:", "Foo:", "Foo", ""),
    ("only OWS", "Foo: \t \t ", "Foo", ""), ("two lines, one name", "my-key: 1\x0d\nmy-Key: 2", "my-key", "1|2")
  ] fun (_, line, name, want) =>
    checkHandler s!"GET / HTTP/1.1\x0d\nHost: example.com\x0d\n{line}\x0d\nConnection: close\x0d\n\x0d\n" (fieldValues name) (.body want)

/-! ## Hostile heads (RFC 9112 §2.2, §3) -/

#eval checkCases "Inputs that are not an HTTP/1.1 request" #[
    ("TLS 1.2 client hello prefix", ByteArray.mk #[0x16, 0x03, 0x01, 0x00, 0xa5, 0x01, 0x00, 0x00], Want.exact r400),
    ("TLS 1.3 client hello prefix", ByteArray.mk #[0x16, 0x03, 0x03, 0x00, 0x7c, 0x01, 0x00, 0x00], .exact r400),
    -- The version is checked before the method, so the preface gets 505 (RFC 9110 §15.6.6).
    ("HTTP/2 connection preface", "PRI * HTTP/2.0\x0d\n\x0d\nSM\x0d\n\x0d\n".toUTF8, .exact r505),
    ("HTTP response sent as a request", "HTTP/1.1 200 OK\x0d\nContent-Length: 2\x0d\n\x0d\nok".toUTF8, .exact r400),
    ("Bare LF line endings", "GET / HTTP/1.1\nHost: example.com\n\n".toUTF8, .exact r400),
    ("CR-only line endings", "GET / HTTP/1.1\x0dHost: example.com\x0d\x0d".toUTF8, .exact r400),
    ("Null bytes everywhere", ByteArray.mk #[0x00, 0x00, 0x00, 0x00], .exact r400),
    ("CRLF injection attempt in request-line",
      "GET /path%0d%0aInjected: header HTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n".toUTF8, .exact r400),
    ("Unicode in path (raw multibyte UTF-8)", "GET /caf\xc3\xa9 HTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n".toUTF8, .exact r400),
    ("Extremely long method token",
      (String.ofList (List.replicate 8192 'A') ++ " / HTTP/1.1\x0d\nHost: h\x0d\n\x0d\n").toUTF8, .exact r501),
    ("absolute-form target naming an internal address",
      "GET http://169.254.169.254/latest/meta-data/ HTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n".toUTF8, .status "HTTP/1.1 200")
  ] fun (_, raw, want) => do want.check (← serveBytes raw okHandler (closeInput := true))


#eval checkCases "The HTTP/2 preface never reaches the handler" #[
    ("PRI * HTTP/2.0", do
      let (r, seen) ← serveRecording "PRI * HTTP/2.0\x0d\n\x0d\nSM\x0d\n\x0d\n" (closeInput := true)
      ensure seen.isEmpty "the handler ran"
      (Want.status "HTTP/1.1 505").check r)
  ] (·.2)
