import Std.Http

open Std Http
open Std.Http.Protocol.H1

/-!
Tests that a server reads `Expect` as a list (RFC 9110 §10.1.1, §5.6.1): a request whose `Expect`
field lines have the member `100-continue`, in any case, next to other members or on two lines,
waits for a `100 Continue` decision. Members are split at the commas outside quoted strings, so a
`100-continue` inside a quoted string, or one with a value, is no expectation. A request with only
other expectations is served normally, and an HTTP/1.0 request never waits. Every prefix of each head
and every split of it into two reads gives the answer of the whole head.
-/

def check (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw (IO.userError msg)

/--
Feeds `parts` to a server, stepping after each, and returns whether it waits for a `100-continue`
decision, whether it reported `.continue`, and its error.
-/
def run (parts : List String) : Bool × Bool × Option Error := Id.run do
  let mut m : Machine .receiving := { config := {} }
  let mut reported := false
  for p in parts do
    m := m.feed p.toUTF8
    for _ in [0:4] do
      let (m', r) := m.step
      m := m'
      reported := reported || r.events.any (· matches .«continue»)
  (m.isReaderAwaitingContinue, reported, m.error)

/--
The head with `fields` asks for `100 Continue` exactly when `expects`; its prefixes never do, and
every split into two reads agrees with the whole head.
-/
def checkExpect (name fields : String) (expects : Bool) (version := "1.1") : IO Unit := do
  let head := s!"POST / HTTP/{version}\r\nHost: a\r\nContent-Length: 5\r\n{fields}\r\n"
  let whole := run [head]
  check (whole == (expects, expects, none))
    s!"{name}: expected awaiting continue = {expects}, got {repr whole}"
  let chars := head.toList
  for i in [1:chars.length] do
    let first := String.ofList (chars.take i)
    let second := String.ofList (chars.drop i)
    let (awaiting, reported, err) := run [first]
    check (!awaiting && !reported && err.isNone)
      s!"{name}: the prefix of {i} bytes already decided: {repr (awaiting, reported, err)}"
    check (run [first, second] == whole) s!"{name}: split at {i} gives {repr (run [first, second])}"

/-- Runs every case and throws once, listing the failures. -/
def runCases (cases : List (IO Unit)) : IO Unit := do
  let mut errors : Array String := #[]
  for c in cases do
    try c catch e => errors := errors.push (toString e)
  unless errors.isEmpty do throw (IO.userError ("\n".intercalate errors.toList))

#eval runCases [
  checkExpect "alone" "Expect: 100-continue\r\n" true,
  checkExpect "first of two members" "Expect: 100-continue, x\r\n" true,
  checkExpect "second member, other case" "Expect: x, 100-CONTINUE\r\n" true,
  checkExpect "empty list elements" "Expect: ,100-continue,\r\n" true,
  checkExpect "two field lines" "Expect: 100-continue\r\nExpect: 100-continue\r\n" true,
  checkExpect "on a later field line" "Expect: x\r\nExpect: 100-continue\r\n" true,
  checkExpect "inside a quoted string" "Expect: a=\"b, 100-continue\"\r\n" false,
  checkExpect "after an escaped quote" "Expect: a=\"b\\\", 100-continue\"\r\n" false,
  checkExpect "a quoted member" "Expect: \"100-continue\"\r\n" false,
  checkExpect "with a value" "Expect: 100-continue=x\r\n" false,
  checkExpect "only another expectation" "Expect: x\r\n" false,
  checkExpect "HTTP/1.0" "Expect: 100-continue, x\r\n" false (version := "1.0"),
  checkExpect "no Expect" "" false]
