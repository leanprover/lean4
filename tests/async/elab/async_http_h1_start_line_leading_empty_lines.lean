import Std.Http

open Std Http
open Std.Http.Protocol.H1

/-!
Tests that the empty lines a server ignores before a request line (RFC 9112 §2.2) do not count toward
`maxStartLineLength`: a request line that fits the limit is accepted after up to
`maxLeadingEmptyLines` empty lines, alone or after another request on the connection, and one byte
longer gets 414 however many empty lines come first. Each input is checked whole, as every 2-read
split, and as every prefix fed one byte per read.
-/

def check (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw (IO.userError msg)

def config : Protocol.H1.Config := { maxStartLineLength := 64, maxUriLength := 64 }

/-- Steps the machine until it stops making progress, answering each complete request with a 200. -/
def settle (m : Machine .receiving) (out : ByteArray) (pending : Bool) :
    Machine .receiving × ByteArray × Bool := Id.run do
  let mut m := m
  let mut out := out
  let mut pending := pending
  for _ in [0:16] do
    let (m', r) := m.step
    m := m'
    out := out ++ r.output.toByteArray
    for e in r.events do
      if e matches .endHeaders _ then pending := true
    while m.canPullBody do
      let (m', chunk?) := m.pullBody
      m := m'
      if chunk?.isNone then break
    if pending && m.isReaderComplete then
      m := m.send { status := .ok } |>.setKnownSize (.fixed 0) |>.userClosedBody
      pending := false
  (m, out, pending)

/-- The error and the number of 200 answers after a server reads `parts`. -/
def serve (parts : List ByteArray) : Option Error × Nat := Id.run do
  let mut m : Machine .receiving := { config }
  let mut out := ByteArray.empty
  let mut pending := false
  for p in parts do
    (m, out, pending) := settle (m.feed p) out pending
  (m.error, ((String.fromUTF8! out).splitOn "HTTP/1.1 200 ").length - 1)

/--
`input` read whole must give `expected`, and so must every 2-read split. Every prefix fed one byte
per read must fail or wait as that prefix read whole does.
-/
def sameEverywhere (name : String) (input : String) (expected : Option Error × Nat) : IO Unit := do
  let input := input.toUTF8
  let whole := serve [input]
  check (whole == expected) s!"{name}: expected {repr expected}, got {repr whole}"
  for i in [1:input.size] do
    let split := serve [input.extract 0 i, input.extract i input.size]
    check (split == whole) s!"{name}: a split after byte {i} gives {repr split}, whole gives {repr whole}"
  for i in [1:input.size + 1] do
    let pre := input.extract 0 i
    let drip := serve ((List.range i).map fun j => pre.extract j (j + 1))
    check (drip == serve [pre]) s!"{name}: the first {i} bytes one per read give {repr drip}"

def runCases (cases : List (IO Unit)) : IO Unit := do
  let mut errors : Array String := #[]
  for c in cases do
    try c catch e => errors := errors.push (toString e)
  unless errors.isEmpty do throw (IO.userError ("\n".intercalate errors.toList))

def repeatStr (s : String) (n : Nat) : String := String.join (List.replicate n s)

/-- A request line of `n` bytes, its CRLF included, followed by the rest of a head. -/
def request (n : Nat) : String :=
  "GET /" ++ repeatStr "a" (n - 16) ++ " HTTP/1.1\r\nHost: a\r\n\r\n"

def get : String := "GET / HTTP/1.1\r\nHost: a\r\n\r\n"

#eval runCases <| List.flatten <| [0, 1, 2, 8].map fun k =>
  let lead := repeatStr "\r\n" k
  [sameEverywhere s!"{k} empty lines, a 63-byte line" (lead ++ request 63) (none, 1),
   sameEverywhere s!"{k} empty lines, a 64-byte line" (lead ++ request 64) (none, 1),
   sameEverywhere s!"{k} empty lines, a 65-byte line" (lead ++ request 65) (some .uriTooLong, 0),
   sameEverywhere s!"a request, {k} empty lines, a 64-byte line" (get ++ lead ++ request 64) (none, 2),
   sameEverywhere s!"a request, {k} empty lines, a 65-byte line" (get ++ lead ++ request 65) (some .uriTooLong, 1)]

#eval runCases [
  sameEverywhere "9 empty lines" (repeatStr "\r\n" 9 ++ request 20) (some .badMessage, 0)]
