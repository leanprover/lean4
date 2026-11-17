import Std.Http

open Std Http
open Std.Http.Protocol.H1

/-!
Tests that a client reads a response whose status code is outside 100–599 as
`500 Internal Server Error`: RFC 9110 §15 asks a client to process a response with an invalid status
code as a 5xx. This covers the codes above 599 as well as those below 100. Valid codes, including
unregistered ones such as 599, are kept. Each response is read whole, one byte per read, split into
two reads at every point, and cut short at every point.
-/

def check (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw (IO.userError msg)

/--
Sends a GET, feeds `parts` as the response, stepping after each, and returns the status codes of
the response heads read and the machine's error.
-/
def client (parts : List String) : Array Nat × Option Error := Id.run do
  let mut m : Machine .sending := ({ config := {} } : Machine .sending).send
    { method := .get, version := .v11, uri := RequestTarget.originForm! "/",
      headers := Headers.empty.insert! "Host" "a" } |>.userClosedBody
  let mut codes : Array Nat := #[]
  for p in parts do
    m := m.feed p.toUTF8
    for _ in [0:8] do
      let (m', r) := m.step
      m := m'
      for e in r.events do
        if let .endHeaders head := e then codes := codes.push head.status.toCode.toNat
      while m.canPullBody do
        let (m', chunk?) := m.pullBody
        m := m'
        if chunk?.isNone then break
  (codes, m.error)

/-- Every way to read `input`: whole, one byte per read, and every split into two reads. -/
def readings (input : String) : List (List String) :=
  let chars := input.toList
  let splits := (List.range (chars.length + 1)).map fun i =>
    [String.ofList (chars.take i), String.ofList (chars.drop i)]
  [input] :: chars.map (String.singleton ·) :: splits

/-- Every reading of `statusLine` with an empty body is read as one response with status `code`, and
no prefix of it fails or reads another status. -/
def expectStatus (statusLine : String) (code : Nat) : IO Unit := do
  let input := statusLine ++ "\r\nContent-Length: 0\r\n\r\n"
  for parts in readings input do
    let (codes, err) := client parts
    check (codes == #[code] && err.isNone)
      s!"{statusLine.quote}, reads {parts.map String.quote}: expected status {code}, got {codes} {repr err}"
  for i in [0:input.length] do
    let (codes, err) := client [String.ofList (input.toList.take i)]
    check (codes.all (· == code) && err.isNone)
      s!"{statusLine.quote}, prefix of {i}: got {codes} {repr err}"

def runCases (cases : List (IO Unit)) : IO Unit := do
  let mut errors : Array String := #[]
  for c in cases do
    try c catch e => errors := errors.push (toString e)
  unless errors.isEmpty do throw (IO.userError ("\n".intercalate errors.toList))

#eval runCases [
  -- Invalid codes are read as 500.
  expectStatus "HTTP/1.1 600 X" 500,
  expectStatus "HTTP/1.1 600" 500,
  expectStatus "HTTP/1.1 777 Custom" 500,
  expectStatus "HTTP/1.1 999 X" 500,
  expectStatus "HTTP/1.1 000 X" 500,
  expectStatus "HTTP/1.1 099 X" 500,
  -- Valid codes are kept, registered or not.
  expectStatus "HTTP/1.1 599 X" 599,
  expectStatus "HTTP/1.1 500 Internal Server Error" 500,
  expectStatus "HTTP/1.1 404 Not Found" 404,
  expectStatus "HTTP/1.1 200 OK" 200
]
