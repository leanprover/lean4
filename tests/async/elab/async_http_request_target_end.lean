import Std.Http

open Std Http
open Std.Http.Protocol.H1

/-!
Regression test for #16479: the HTTP/1.1 server machine rejects a request line as soon as its
request-target meets a byte that no request-target contains (RFC 9112 §3.2, RFC 3986), such as the
CR or LF of a line with no SP after the target. It does not wait for an SP or for `maxUriLength`
bytes. RFC 9112 §3: "Recipients of an invalid request-line SHOULD respond with either a 400 (Bad
Request) error or a 301 (Moved Permanently) redirect".

Each request is fed as every prefix and as two reads split at every byte boundary, so the answer
does not depend on where a read ends (#16035).
-/

/-- Feeds `parts` in order, stepping after each, and returns the machine's error and its output. -/
def feedParts (parts : List ByteArray) (config : Protocol.H1.Config := {}) :
    Option Error × String := Id.run do
  let mut m : Machine .receiving := { config }
  let mut out := ByteArray.empty
  for part in parts do
    m := m.feed part
    for _ in [0:4] do
      let (m', r) := m.step
      m := m'
      out := out ++ r.output.toByteArray
  return (m.error, String.fromUTF8! out)

def check (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw (IO.userError msg)

/--
`waits ++ rest` is a request whose request-target is ended or broken by the first byte of `rest`.
Every prefix of at most `waits.size` bytes gets no answer yet. Every longer prefix, and the whole
input split at any byte boundary, fails with `error` and gets `status`.
-/
def expectRejectedAt (name : String) (waits rest : ByteArray) (error : Error) (status : String)
    (config : Protocol.H1.Config := {}) : IO Unit := do
  let whole := waits ++ rest
  for i in [0:whole.size + 1] do
    let pfx := whole.extract 0 i
    let (err, out) := feedParts [pfx] config
    if i ≤ waits.size then
      check (err.isNone && out.isEmpty)
        s!"{name}: after {i} bytes expected no answer yet, got {repr err} {out.quote}"
    else
      check (err == some error && out.startsWith status)
        s!"{name}: after {i} bytes expected {repr error} and {status.quote}, got {repr err} {out.quote}"
    let (err, out) := feedParts [pfx, whole.extract i whole.size] config
    check (err == some error && out.startsWith status)
      s!"{name}: split at byte {i}, expected {repr error} and {status.quote}, got {repr err} {out.quote}"

def expect400 (name : String) (waits rest : String) (config : Protocol.H1.Config := {}) : IO Unit :=
  expectRejectedAt name waits.toUTF8 rest.toUTF8 .badMessage "HTTP/1.1 400 Bad Request\r\n" config

/-- Runs every case and throws once, listing the first failure of each failing case. -/
def runCases (cases : List (IO Unit)) : IO Unit := do
  let mut errors : Array String := #[]
  for c in cases do
    try c catch e => errors := errors.push (toString e)
  unless errors.isEmpty do throw (IO.userError ("\n".intercalate errors.toList))

def repeatStr (s : String) (n : Nat) : String := String.join (List.replicate n s)

def expectAccepted (name req : String) (config : Protocol.H1.Config := {}) : IO Unit := do
  let (err, out) := feedParts [req.toUTF8] config
  check (err.isNone && out.isEmpty) s!"{name}: expected no error, got {repr err} {out.quote}"

#eval runCases [
  expectAccepted "origin-form" "GET /x HTTP/1.1\r\nHost:a\r\n\r\n",
  expectAccepted "absolute-form" "GET http://a/x HTTP/1.1\r\nHost:a\r\n\r\n",
  expectAccepted "asterisk-form" "OPTIONS * HTTP/1.1\r\nHost:a\r\n\r\n"]

-- No SP follows the target anywhere in these inputs, so only the line end can reject them.
#eval runCases [
  expect400 "no SP before the version" "GET /xHTTP/1.1" "\r\nHost:a\r\n\r\n",
  expect400 "CR instead of the SP" "GET /x" "\rHTTP/1.1\r\nHost:a\r\n\r\n",
  expect400 "line ends after the target" "GET /x" "\r\nHost:a\r\n\r\n",
  expect400 "bare LF after the target" "GET /x" "\nHost:a\n\n",
  expect400 "absolute-form, no version" "GET http://a/x" "\r\nHost:a\r\n\r\n",
  expect400 "authority-form, no version" "CONNECT a:443" "\r\nHost:a:443\r\n\r\n",
  expect400 "asterisk-form, no version" "OPTIONS *" "\r\nHost:a\r\n\r\n"]

-- A byte outside the request-target's character set fails the line when it arrives, before any SP.
#eval runCases <| [
    ("HTAB", "\t"), ("VT", "\x0b"), ("FF", "\x0c"), ("NUL", "\x00"), ("ESC", "\x1b"),
    ("DEL", "\x7f"), ("'#'", "#"), ("'\"'", "\""), ("'<'", "<"), ("'>'", ">"), ("'\\'", "\\"),
    ("'^'", "^"), ("'`'", "`"), ("'{'", "{"), ("'|'", "|"), ("'}'", "}"), ("non-ASCII", "é")
  ].map fun (name, byte) =>
    expect400 s!"{name} in the target" "GET /x" s!"{byte}y HTTP/1.1\r\nHost:a\r\n\r\n"

-- `maxUriLength` is 16: `/` and fifteen `a`s fill it.
#eval
  let config : Protocol.H1.Config := { maxUriLength := 16 }
  let full := "GET /" ++ repeatStr "a" 15
  runCases [
    expectAccepted "target at the limit" s!"{full} HTTP/1.1\r\nHost:a\r\n\r\n" config,
    expectRejectedAt "one target byte past the limit" full.toUTF8
      "a HTTP/1.1\r\nHost:a\r\n\r\n".toUTF8 .uriTooLong "HTTP/1.1 414 URI Too Long\r\n" config,
    -- The target is not longer than the limit, so these are 400, not 414.
    expect400 "line ends at the limit" full "\r\nHost:a\r\n\r\n" config,
    expect400 "NUL at the limit" full "\x00 HTTP/1.1\r\nHost:a\r\n\r\n" config]
