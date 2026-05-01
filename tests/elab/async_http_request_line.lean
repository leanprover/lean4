import Std.Http.Test.Helpers

open Std.Async
open Std Http Internal Test

-- Shared fixtures

private def ok200 : String :=
  "HTTP/1.1 200 OK\x0d\nContent-Type: text/plain; charset=utf-8\x0d\nServer: LeanHTTP/1.1\x0d\nConnection: close\x0d\nContent-Length: 2\x0d\n\x0d\nok"

-- RFC 9112 §3: Request Line

#eval runGroup "RFC 9112 §3: request-line parse failures" do
  check "missing version → 400"
    (raw := "GET /\x0d\nHost: example.com\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r r400)

  check "missing URI (double space) → 400"
    (raw := "GET  HTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r r400)

  check "extra spaces in request-line → 400"
    (raw := "GET  /  HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r r400)

  check "whitespace-only request-line → 400"
    (raw := "   \x0d\n\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r r400)

  check "no spaces in request-line → 400"
    (raw := "GETHTTP/1.1\x0d\nHost: example.com\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r r400)

  check "garbage after request-line version → 400"
    (raw := "GET / HTTP/1.1 xxxxxx\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r r400)

  -- Empty connection: no bytes → silent close, no response
  checkClose "empty connection → silent close"
    (raw := "")
    (handler := okHandler)
    (expect := fun r => assertExact r "")

#eval runGroup "RFC 9112 §2.2: leading CRLF before request-line" do
  check "single leading CRLF accepted"
    (raw := "\x0d\nGET / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r ok200)

-- RFC 9112 §9: HTTP version

#eval runGroup "RFC 9112 §9: HTTP version" do
  check "HTTP/2.0 → 505"
    (raw := "GET / HTTP/2.0\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r r505)

-- RFC 9110 §9: Methods

#eval runGroup "RFC 9110 §9: method validation" do
  check "unknown method FOOBAR → 400"
    (raw := "FOOBAR / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r r400)

  check "lowercase method → 400"
    (raw := "get / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r r400)

  check "non-ASCII method → 400"
    (raw := "GÉT / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r r400)

  check "very long unrecognized method → 400"
    (raw :=
      let m := String.ofList (List.replicate 20 'G')
      s!"{m} / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r r400)

  check "token method with hyphen (X-CUSTOM) → 400"
    (raw := "X-CUSTOM / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r r400)

-- RFC 9112 §3.2: Request target forms

#eval runGroup "RFC 9112 §3.2: request target forms" do
  check "GET authority-form → 400"
    (raw := "GET example.com:443 HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r r400)

  check "CONNECT authority-form accepted"
    (raw := "CONNECT example.com:443 HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r ok200)

  check "CONNECT authority-form port mismatch → 400"
    (raw := "CONNECT example.com:444 HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r r400)

  check "GET asterisk-form → 400"
    (raw := "GET * HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r r400)

  check "OPTIONS * accepted"
    (raw := "OPTIONS * HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r ok200)

  check "absolute-form URI accepted"
    (raw := "GET http://example.com/path HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r ok200)

-- RFC 9112 §3.3: Early invalid bytes

#eval runGroup "RFC 9112 §3: early invalid bytes" do
  checkClose "NUL byte → 400"
    (raw := "\x00")
    (handler := okHandler)
    (expect := fun r => assertExact r r400)

  checkClose "SP byte → 400"
    (raw := "\x20")
    (handler := okHandler)
    (expect := fun r => assertExact r r400)

  checkClose "TLS client-hello prefix → 400"
    (raw := "\x16\x03\x01\x00\xa5")
    (handler := okHandler)
    (expect := fun r => assertExact r r400)

-- RFC 7230 §5.4: Host header

#eval runGroup "RFC 7230 §5.4: Host header" do
  check "missing Host header → 400"
    (raw := "GET / HTTP/1.1\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r r400)

  check "empty Host allowed for origin-form"
    (raw := "GET / HTTP/1.1\x0d\nHost: \x0d\nConnection: close\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r ok200)

  check "multiple Host headers → 400"
    (raw := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nHost: other.com\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r r400)

  check "absolute-form: URI authority takes precedence over Host"
    (raw := "GET http://good.example/path HTTP/1.1\x0d\nHost: good.example\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r ok200)
