import Std.Http.Test.Helpers

open Std.Async
open Std Http Internal Test

-- Shared fixtures

private def ok200 : String :=
  "HTTP/1.1 200 OK\x0d\nContent-Type: text/plain; charset=utf-8\x0d\nServer: LeanHTTP/1.1\x0d\nConnection: close\x0d\nContent-Length: 2\x0d\n\x0d\nok"

-- RFC 9112 §5: Header fields — syntax and byte-level validation

#eval runGroup "RFC 9112 §5: header field syntax" do
  check "header without colon → 400"
    (raw := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nBadHeader value\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r r400)

  check "leading whitespace (obs-fold) → 400"
    (raw := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\n X-Bad: folded\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r r400)

  check "space in header name → 400"
    (raw := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nBad Header: value\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r r400)

  check "bare LF line endings → 400"
    (raw := "GET / HTTP/1.1\nHost: example.com\nConnection: close\n\n")
    (handler := okHandler)
    (expect := fun r => assertExact r r400)

  check "tab in header value → accepted"
    (raw := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nX-Tab: value\twith\ttabs\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r ok200)

  check "additional colon in header value stays in value"
    (raw := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nBad:Name: value\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r ok200)

  check "CRLF in header value parsed as two separate headers → 200"
    (raw := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nX-Inject: value\x0d\nEvil: injected\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r ok200)

-- Critical: NUL and control chars in header names/values

#eval runGroup "RFC 9110 §5.5: invalid bytes in header fields (Critical)" do
  check "NUL in header name → 400"
    (raw := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nX-Bad\x00Header: value\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r r400)

  check "NUL in header value → 400"
    (raw := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nX-Header: bad\x00value\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r r400)

  check "control char (0x01) in header value → 400"
    (raw := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nX-Header: bad\x01value\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r r400)

-- RFC 9112 §6.3 / §9110 §8.6: header size limits

#eval runGroup "Header size limits" do
  check "header name > 256 bytes → 400"
    (raw :=
      let longName := String.ofList (List.replicate 257 'X')
      s!"GET / HTTP/1.1\x0d\nHost: example.com\x0d\n{longName}: value\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r r400)

  check "header value too long → 400"
    (raw :=
      let longVal := String.ofList (List.replicate 9000 'x')
      s!"GET / HTTP/1.1\x0d\nHost: example.com\x0d\nX-Long: {longVal}\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r r400)

  check "too many headers (101) → 431"
    (raw := Id.run do
      let mut raw := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n"
      for i in [0:101] do
        raw := raw ++ s!"X-Header-{i}: value{i}\x0d\n"
      return raw ++ "\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r r431)

  check "total header bytes too large → 431"
    (raw := Id.run do
      let mut raw := "GET / HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n"
      let v := String.ofList (List.replicate 200 'a')
      for i in [0:200] do
        raw := raw ++ s!"X-Header-{i}: {v}\x0d\n"
      return raw ++ "\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r r431)

  check "request-line too long → 400"
    (raw :=
      let longUri := "/" ++ String.ofList (List.replicate 2000 'a')
      s!"GET {longUri} HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := okHandler)
    (expect := fun r => assertExact r r400)

#eval runGroup "maxStartLineLength config" do
  let cfg : Config := { defaultConfig with maxStartLineLength := 16384 }

  let segment := String.ofList (List.replicate 255 'a')
  let maxUri := "/" ++ String.intercalate "/" (List.replicate 32 segment)

  check "URI at maxStartLineLength limit → 200"
    (raw := s!"GET {maxUri} HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := okHandler)
    (config := cfg)
    (expect := fun r => assertExact r ok200)

  check "URI one byte over limit → 414"
    (raw := s!"GET {maxUri}/x HTTP/1.1\x0d\nHost: example.com\x0d\nConnection: close\x0d\n\x0d\n")
    (handler := okHandler)
    (config := cfg)
    (expect := fun r => assertStatus r "HTTP/1.1 414")
