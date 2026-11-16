import Std.Http

open Std Http
open Std.Http.Protocol.H1

/-!
Tests that a line which becomes invalid in a later read is rejected when that read arrives, even
though no line feed has arrived yet. The first read ends inside a request line, status line, field
line, chunk-size line or trailer line. The second read adds a byte that cannot continue the line
and no line feed. The answer must be the one the whole input gets at once, not a wait for a line
feed that may never come (the answer must not depend on where a read ends, as in #16035 and #16479).
-/

def check (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw (IO.userError msg)

/-- Runs the machine until it stops making progress, collecting its output. -/
def settle (m : Machine dir) (out : ByteArray) : Machine dir × ByteArray := Id.run do
  let mut m := m
  let mut out := out
  for _ in [0:8] do
    let (m', r) := m.step
    m := m'
    out := out ++ r.output.toByteArray
    while m.canPullBody do
      let (m', chunk?) := m.pullBody
      m := m'
      if chunk?.isNone then break
  (m, out)

/-- Feeds `parts` to a server, settling after each, and returns its error and output. -/
def server (parts : List String) (config : Protocol.H1.Config := {}) : Option Error × String := Id.run do
  let mut m : Machine .receiving := { config }
  let mut out := ByteArray.empty
  for p in parts do
    (m, out) := settle (m.feed p.toUTF8) out
  (m.error, String.fromUTF8! out)

/-- Sends a GET, feeds `parts` as the response, settling after each, and returns the error. -/
def client (parts : List String) : Option Error := Id.run do
  let mut m : Machine .sending := ({ config := {} } : Machine .sending).send
    { method := .get, version := .v11, uri := RequestTarget.originForm! "/",
      headers := Headers.empty.insert! "Host" "a" } |>.userClosedBody
  let mut out := ByteArray.empty
  for p in parts do
    (m, out) := settle (m.feed p.toUTF8) out
  m.error

/-- `first` waits; `first ++ second`, as one read or two, fails with `error` and `status`. -/
def serverRejects (name first second : String) (error : Error) (status : String)
    (config : Protocol.H1.Config := {}) : IO Unit := do
  let (err, out) := server [first] config
  check (err.isNone && out.isEmpty) s!"{name}: the first read alone should wait, got {repr err} {out.quote}"
  for parts in [[first ++ second], [first, second]] do
    let (err, out) := server parts config
    check (err == some error && out.startsWith status)
      s!"{name}, {parts.length} read(s): expected {repr error} and {status.quote}, got {repr err} {out.quote}"

def clientRejects (name first second : String) (error : Error := .badMessage) : IO Unit := do
  check (client [first]).isNone s!"{name}: the first read alone should wait, got {repr (client [first])}"
  for parts in [[first ++ second], [first, second]] do
    let err := client parts
    check (err == some error) s!"{name}, {parts.length} read(s): expected {repr error}, got {repr err}"

/-- Runs every case and throws once, listing the failures. -/
def runCases (cases : List (IO Unit)) : IO Unit := do
  let mut errors : Array String := #[]
  for c in cases do
    try c catch e => errors := errors.push (toString e)
  unless errors.isEmpty do throw (IO.userError ("\n".intercalate errors.toList))

def repeatStr (s : String) (n : Nat) : String := String.join (List.replicate n s)

def head : String := "GET / HTTP/1.1\r\nHost: a\r\n"

def chunked : String := "POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n"

def r400 : String := "HTTP/1.1 400 "

#eval runCases [
  serverRejects "control byte in the request-target" "GET /x" "\x01y" .badMessage r400,
  serverRejects "invalid byte after a method" "GE" "(" .badMessage r400,
  serverRejects "bare CR in the request line" "GET / HTTP/1.1\r" "X" .badMessage r400,
  serverRejects "invalid byte in a field name" s!"{head}X" "(" .badMessage r400,
  serverRejects "control byte in a field value" s!"{head}X: a" "\x01" .badMessage r400,
  serverRejects "bare CR after a field line" "GET / HTTP/1.1\r\nHost: a\r" "X" .badMessage r400,
  serverRejects "bare CR at the end of the head" s!"{head}\r" "." .badMessage r400,
  serverRejects "field value over its limit" s!"{head}X: {repeatStr "v" 16}" "v" .headersTooLarge
    "HTTP/1.1 431 " { maxHeaderValueLength := 16 },
  serverRejects "invalid byte in a chunk size" s!"{chunked}5" "g" .badMessage r400,
  serverRejects "bare CR after the last chunk" s!"{chunked}0\r\n\r" "+" .badMessage r400,
  serverRejects "invalid byte in a trailer name" s!"{chunked}0\r\nT" "(" .badMessage r400]

#eval runCases [
  clientRejects "invalid byte in a status code" "HTTP/1.1 2" "x",
  clientRejects "bare CR at the end of the head" "HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r" "@hi",
  clientRejects "invalid byte in a field name" "HTTP/1.1 200 OK\r\nX" "(",
  clientRejects "bare CR after the last chunk"
    "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n0\r\n\r" "+"]
