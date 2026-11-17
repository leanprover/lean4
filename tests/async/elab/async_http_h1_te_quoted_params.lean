import Std.Http

open Std Http
open Std.Http.Protocol.H1

/-!
Tests that a transfer-parameter whose quoted value contains `,` or `;` is read as one parameter
(RFC 9112 §7, RFC 9110 §5.6.4): `Transfer-Encoding: gzip;level="a,b", chunked` names the codings
`gzip` and `chunked`, so a server that does not decode gzip answers 501, and one that does reads the
body. Malformed quoting (an unterminated quoted-string, a backslash that escapes the rest, text after
the closing quote) stays 400, as do parameters on `chunked`. Each input is checked whole, as every
2-read split, and as every prefix fed one byte per read.
-/

def check (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw (IO.userError msg)

/-- Runs the machine until it stops making progress, collecting its output and the body. -/
def settle (m : Machine .receiving) (out body : ByteArray) : Machine .receiving × ByteArray × ByteArray := Id.run do
  let mut m := m
  let mut out := out
  let mut body := body
  for _ in [0:8] do
    let (m', r) := m.step
    m := m'
    out := out ++ r.output.toByteArray
    while m.canPullBody do
      let (m', chunk?) := m.pullBody
      m := m'
      match chunk? with
      | some c => body := body ++ c.chunk.data
      | none => break
  (m, out, body)

/-- The error, the output and the body after a server reads `parts`. -/
def server (config : Protocol.H1.Config) (parts : List ByteArray) : Option Error × String × String := Id.run do
  let mut m : Machine .receiving := { config }
  let mut out := ByteArray.empty
  let mut body := ByteArray.empty
  for p in parts do
    (m, out, body) := settle (m.feed p) out body
  (m.error, String.fromUTF8! out, String.fromUTF8! body)

/--
`input` read whole must end with `expected` (`none`: no error and the body `body`) and an output
starting with `status`, and so must every 2-read split. Every prefix fed one byte per read must fail
or wait as that prefix read whole does.
-/
def sameEverywhere (name : String) (config : Protocol.H1.Config) (input : String)
    (expected : Option Error) (status : String) (body : String := "") : IO Unit := do
  let input := input.toUTF8
  let run := server config
  let whole := run [input]
  check (whole.1 == expected && whole.2.1.startsWith status && (expected.isSome || whole.2.2 == body))
    s!"{name}: expected {repr expected} {status.quote} {body.quote}, got {repr whole.1} {whole.2.1.quote} {whole.2.2.quote}"
  for i in [1:input.size] do
    let split := run [input.extract 0 i, input.extract i input.size]
    check (split == whole) s!"{name}: a split after byte {i} gives {repr split.1}, whole gives {repr whole.1}"
  for i in [1:input.size + 1] do
    let pre := input.extract 0 i
    let drip := run ((List.range i).map fun j => pre.extract j (j + 1))
    let once := run [pre]
    check (drip.1 == once.1 && drip.2.1 == once.2.1)
      s!"{name}: the first {i} bytes one per read give {repr drip.1}, one read gives {repr once.1}"

/-- Runs every case and throws once, listing the failures. -/
def runCases (cases : List (IO Unit)) : IO Unit := do
  let mut errors : Array String := #[]
  for c in cases do
    try c catch e => errors := errors.push (toString e)
  unless errors.isEmpty do throw (IO.userError ("\n".intercalate errors.toList))

def repeatStr (s : String) (n : Nat) : String := String.join (List.replicate n s)

def req (te : String) : String :=
  s!"POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: {te}\r\n\r\n5\r\nhello\r\n0\r\n\r\n"

def gzip : Protocol.H1.Config := { acceptedTransferCodings := #["gzip"] }
def r400 := "HTTP/1.1 400 "
def r501 := "HTTP/1.1 501 "

#eval runCases [
  sameEverywhere "comma in a quoted value" {} (req "gzip;level=\"a,b\", chunked") (some .unsupportedTransferCoding) r501,
  sameEverywhere "semicolon in a quoted value" {} (req "gzip;level=\"a;b\", chunked") (some .unsupportedTransferCoding) r501,
  sameEverywhere "escaped quote and comma" {} (req "gzip;level=\"a\\\",b\", chunked") (some .unsupportedTransferCoding) r501,
  sameEverywhere "comma in a quoted value, gzip accepted" gzip (req "gzip;level=\"a,b\", chunked") none "" "hello",
  sameEverywhere "semicolon in a quoted value, gzip accepted" gzip (req "gzip; level = \"a;b\" ;x=y, chunked") none "" "hello",
  sameEverywhere "token value, gzip accepted" gzip (req "gzip;level=1, chunked") none "" "hello",
  sameEverywhere "unterminated quoted value" gzip (req "gzip;level=\"a, chunked") (some .badMessage) r400,
  sameEverywhere "text after the closing quote" gzip (req "gzip;level=\"a\"b, chunked") (some .badMessage) r400,
  sameEverywhere "backslash before the end" gzip (req "gzip;level=\"a\\, chunked") (some .badMessage) r400,
  sameEverywhere "empty parameter" gzip (req "gzip;, chunked") (some .badMessage) r400,
  sameEverywhere "parameter on chunked" gzip (req "gzip, chunked;q=\"a,b\"") (some .badMessage) r400,
  sameEverywhere "quoted coding name" gzip (req "\"gzip\", chunked") (some .badMessage) r400]
