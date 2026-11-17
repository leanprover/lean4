import Std.Http

open Std Http
open Std.Http.Protocol.H1

/-!
Tests that line ends a server reads before a request line get the same answer whether the end of
input arrives in the same read or later. Empty lines (`CRLF`) before a request line are ignored up to
`maxLeadingEmptyLines`, so a connection that ends after them closes cleanly. A bare `LF`, a `CR` not
followed by `LF`, or more empty lines than the limit get 400 when they arrive before the end of input.
They must get 400 when the end of input arrives with them too, not a clean close: the answer must not
depend on where a read ends (RFC 9112 §2.2).
-/

def check (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw (IO.userError msg)

/--
Steps the machine until it stops making progress, pulling body data and answering each complete
request with an empty 200.
-/
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

/--
Feeds `parts` to a server, settling after each. The end of input is signalled with the last part
(`eofLater := false`) or after it has been read (`eofLater := true`). Returns the error, the number
of 200 answers, whether a 400 was written, and whether the connection ended cleanly (no error, reader
closed).
-/
def serve (parts : List String) (eofLater : Bool) : Option Error × Nat × Bool × Bool := Id.run do
  let mut m : Machine .receiving := { config := {} }
  let mut out := ByteArray.empty
  let mut pending := false
  let mut i := 0
  for p in parts do
    i := i + 1
    m := m.feed p.toUTF8
    if !eofLater && i == parts.length then m := m.noMoreInput
    (m, out, pending) := settle m out pending
  if eofLater || parts.isEmpty then
    (m, out, pending) := settle m.noMoreInput out pending
  let s := String.fromUTF8! out
  (m.error, (s.splitOn "HTTP/1.1 200 ").length - 1, (s.splitOn "HTTP/1.1 400 ").length > 1,
    m.error.isNone && m.isReaderClosed)

/-- Every way to read `input`: whole, one byte per read, and every split into two reads. -/
def readings (input : String) : List (List String) :=
  let chars := input.toList
  let bytes := chars.map (String.singleton ·)
  let splits := (List.range (chars.length + 1)).map fun i =>
    [String.ofList (chars.take i), String.ofList (chars.drop i)]
  [input] :: bytes :: splits

def describe (r : Option Error × Nat × Bool × Bool) : String :=
  s!"error {repr r.1}, {r.2.1} × 200, 400 written: {r.2.2.1}, ended cleanly: {r.2.2.2}"

/-- Every reading of `input`, with the end of input in the last read or after it, gets `expected`. -/
def expect (name input : String) (expected : Option Error × Nat × Bool × Bool) : IO Unit := do
  for parts in readings input do
    for eofLater in [false, true] do
      let got := serve parts eofLater
      check (got == expected)
        s!"{name}, reads {parts.map String.quote}, end of input {if eofLater then "later" else "with the last read"}: expected {describe expected}, got {describe got}"

def runCases (cases : List (IO Unit)) : IO Unit := do
  let mut errors : Array String := #[]
  for c in cases do
    try c catch e => errors := errors.push (toString e)
  unless errors.isEmpty do throw (IO.userError ("\n".intercalate errors.toList))

def repeatStr (s : String) (n : Nat) : String := String.join (List.replicate n s)

def request : String := "GET / HTTP/1.1\r\nHost: a\r\n\r\n"

def closesCleanly (answers : Nat) : Option Error × Nat × Bool × Bool := (none, answers, false, true)

def rejects (answers : Nat) : Option Error × Nat × Bool × Bool := (some .badMessage, answers, true, false)

/-- Line ends a server ignores before a request line: the connection then ends cleanly. -/
def ignored : List (String × String) := [
  ("no bytes", ""),
  ("a CR", "\r"),
  ("one empty line", "\r\n"),
  ("an empty line and a CR", "\r\n\r"),
  ("eight empty lines", repeatStr "\r\n" 8)
]

/-- Line ends a server rejects before a request line. -/
def rejected : List (String × String) := [
  ("a bare LF", "\n"),
  ("an empty line and a bare LF", "\r\n\n"),
  ("a CR and a CR", "\r\r"),
  ("a bare LF and a CR", "\n\r"),
  ("nine empty lines", repeatStr "\r\n" 9),
  ("forty empty lines", repeatStr "\r\n" 40)
]

#eval runCases <|
  (ignored.map fun (name, tail) => expect s!"{name} alone" tail (closesCleanly 0)) ++
  (ignored.map fun (name, tail) => expect s!"{name} after a request" (request ++ tail) (closesCleanly 1)) ++
  (rejected.map fun (name, tail) => expect s!"{name} alone" tail (rejects 0)) ++
  (rejected.map fun (name, tail) => expect s!"{name} after a request" (request ++ tail) (rejects 1))
