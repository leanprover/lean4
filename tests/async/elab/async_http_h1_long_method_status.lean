import Std.Http

open Std Http
open Std.Http.Protocol.H1

/-!
Tests that a request line with a method longer than any method (64 bytes) gets 400 when the line is
malformed and 501 only when the rest of the line is valid, as a shorter unrecognized method does
(RFC 9112 §3, RFC 9110 §9.1). A method longer still than `maxStartLineLength` fails at once with 501
(RFC 9112 §3). Each input is checked whole, as every 2-read split, and as every prefix fed one byte
per read.
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

def r400 := "HTTP/1.1 400 "
def r501 := "HTTP/1.1 501 "

#eval runCases [
  sameEverywhere "65-byte method, control byte in the target" {} s!"{repeatStr "A" 65} /\x01 HTTP/1.1\r\n" (some .badMessage) r400,
  sameEverywhere "200-byte method, two spaces" {} s!"{repeatStr "A" 200}  / HTTP/1.1\r\n" (some .badMessage) r400,
  sameEverywhere "65-byte method, no version" {} s!"{repeatStr "A" 65} /\r\n" (some .badMessage) r400,
  sameEverywhere "65-byte method, bad version" {} s!"{repeatStr "A" 65} / HTTP/x.1\r\n" (some .badMessage) r400,
  sameEverywhere "65-byte method then NUL" {} s!"{repeatStr "A" 65}\x00 / HTTP/1.1\r\n" (some .badMessage) r400,
  sameEverywhere "64-byte method, control byte in the target" {} s!"{repeatStr "A" 64} /\x01 HTTP/1.1\r\n" (some .badMessage) r400,
  sameEverywhere "65-byte method, valid line" {} s!"{repeatStr "A" 65} / HTTP/1.1\r\nHost: a\r\n\r\n" (some .unsupportedMethod) r501,
  sameEverywhere "300-byte method, valid line" {} s!"{repeatStr "A" 300} / HTTP/1.1\r\nHost: a\r\n\r\n" (some .unsupportedMethod) r501,
  sameEverywhere "64-byte method, valid line" {} s!"{repeatStr "A" 64} / HTTP/1.1\r\nHost: a\r\n\r\n" (some .unsupportedMethod) r501,
  sameEverywhere "method past maxStartLineLength" { maxStartLineLength := 100 } s!"{repeatStr "A" 170} /\x01 HTTP/1.1\r\n" (some .unsupportedMethod) r501,
  sameEverywhere "method within maxStartLineLength" { maxStartLineLength := 100 } s!"{repeatStr "A" 150} /\x01 HTTP/1.1\r\n" (some .badMessage) r400,
  sameEverywhere "known method" {} "GET / HTTP/1.1\r\nHost: a\r\n\r\n" none ""]
