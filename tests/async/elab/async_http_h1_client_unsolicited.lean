import Std.Http

open Std Http
open Std.Http.Protocol.H1

/-!
Tests what a client does with bytes that arrive while it has no request outstanding: before its first
request, after a response is complete, or between exchanges. They answer no request, so they must not
be read as the response to the next one (RFC 9112 §9.2; §6.3 forbids reading the data left after a
response as a separate response). The machine fails and sends nothing more, except for bare line
breaks, which are discarded. Every case is fed whole, as every 2-read split, and as every prefix.
-/

def check (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw (IO.userError msg)

/-- Runs the machine until it stops making progress, collecting its output, bodies and the status
of each response head. -/
def settle (m : Machine .sending) (out body : ByteArray) (heads : Array Nat) :
    Machine .sending × ByteArray × ByteArray × Array Nat := Id.run do
  let mut m := m
  let mut out := out
  let mut body := body
  let mut heads := heads
  for _ in [0:8] do
    let (m', r) := m.step
    m := m'
    out := out ++ r.output.toByteArray
    for e in r.events do
      if let .endHeaders h := e then heads := heads.push h.status.toCode.toNat
    while m.canPullBody do
      let (m', chunk?) := m.pullBody
      m := m'
      match chunk? with
      | some c => body := body ++ c.chunk.data
      | none => break
  (m, out, body, heads)

def request (method : Method := .get) : Request.Head :=
  { method, version := .v11, uri := RequestTarget.originForm! "/",
    headers := Headers.empty.insert! "Host" "a" }

structure Run where
  error : Option Error
  requests : Nat
  heads : Array Nat
  body : String

/-- Sends `method` (unless `before`), feeds `parts` with a settle after each, then (with `second`)
sends a GET and feeds `next`, the response to that GET. -/
def run (parts : List ByteArray) (method : Method := .get) (before := false) (next := "")
    (second := true) : Run := Id.run do
  let mut m : Machine .sending := { config := {} }
  unless before do m := m.send (request method) |>.userClosedBody
  let mut out := ByteArray.empty
  let mut body := ByteArray.empty
  let mut heads := #[]
  for p in parts do
    (m, out, body, heads) := settle (m.feed p) out body heads
  if before then
    m := m.send (request method) |>.userClosedBody
    (m, out, body, heads) := settle m out body heads
  if second then
    m := m.send (request .get) |>.userClosedBody
    (m, out, body, heads) := settle m out body heads
    (m, out, body, heads) := settle (m.feed next.toUTF8) out body heads
  let text := String.fromUTF8! out
  { error := m.error, requests := (text.splitOn " HTTP/1.1\r\n").length - 1, heads,
    body := String.fromUTF8! body }

def splits (b : ByteArray) : List (List ByteArray) :=
  [b] :: (List.range (b.size - 1)).map fun i => [b.extract 0 (i + 1), b.extract (i + 1) b.size]

def same (a b : Run) : Bool :=
  a.error == b.error && a.requests == b.requests && a.heads == b.heads && a.body == b.body

def describe (r : Run) : String :=
  s!"error {repr r.error}, {r.requests} request(s) written, heads {r.heads}, body {r.body.quote}"

/-- Every split gives `expected`, and the reads before the last never fail. -/
def runCase (name : String) (input : String) (expected : Run) (method : Method := .get)
    (before := false) (next := "") : IO Unit := do
  for parts in splits input.toUTF8 do
    let r := run parts method before next
    check (same r expected)
      s!"{name}, {parts.length} read(s): expected {describe expected}, got {describe r}"
  for i in [1:input.utf8ByteSize] do
    let r := run [input.toUTF8.extract 0 i] method before (second := false)
    check (r.error.isNone || r.error == expected.error)
      s!"{name}: the prefix of {i} bytes fails with {repr r.error}"

def runCases (cases : List (IO Unit)) : IO Unit := do
  let mut errors : Array String := #[]
  for c in cases do
    try c catch e => errors := errors.push (toString e)
  unless errors.isEmpty do throw (IO.userError ("\n".intercalate errors.toList))

def ok1 : String := "HTTP/1.1 200 OK\r\nContent-Length: 1\r\n\r\na"
def ok2 : String := "HTTP/1.1 200 OK\r\nContent-Length: 1\r\n\r\nb"

#eval runCases [
  -- A response that arrives with the previous one answers no request yet.
  runCase "second response in the same reads" (ok1 ++ ok2)
    { error := some .badMessage, requests := 1, heads := #[200], body := "a" },
  -- The body a server must not send after a HEAD response is not the next response.
  runCase "body after a HEAD response" "HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhello"
    { error := some .badMessage, requests := 1, heads := #[200], body := "" } (method := .head),
  runCase "bytes past Content-Length" "HTTP/1.1 200 OK\r\nContent-Length: 1\r\n\r\naHTTP/1.1 4"
    { error := some .badMessage, requests := 1, heads := #[200], body := "a" },
  runCase "a 408 before the first request" "HTTP/1.1 408 Request Timeout\r\nContent-Length: 0\r\n\r\n"
    { error := some .badMessage, requests := 0, heads := #[], body := "" } (before := true),
  -- Line breaks alone are discarded, and the next response is read once its request is sent.
  runCase "CRLF after a response" (ok1 ++ "\r\n")
    { error := none, requests := 2, heads := #[200, 200], body := "ab" } (next := ok2),
  runCase "CRLF before the first request" "\r\n\r\n"
    { error := none, requests := 1, heads := #[200], body := "a" } (before := true)
    (next := ok1 ++ "\r\n"),
  -- Unchanged: an interim and the final response arrive together.
  runCase "100 and the final response" ("HTTP/1.1 100 Continue\r\n\r\n" ++ ok1)
    { error := none, requests := 2, heads := #[100, 200, 200], body := "ab" } (next := ok2),
  -- Unchanged: after `Connection: close` or a tunnel, what follows is not read at all.
  runCase "Connection: close and more bytes"
    "HTTP/1.1 200 OK\r\nConnection: close\r\nContent-Length: 1\r\n\r\naHTTP/1.1 200 OK\r\n"
    { error := none, requests := 1, heads := #[200], body := "a" },
  runCase "tunnel bytes after a 2xx to CONNECT" "HTTP/1.1 200 OK\r\n\r\nHTTP/1.1 200 OK\r\n"
    { error := none, requests := 1, heads := #[200], body := "" } (method := .connect)]

-- Bytes fed while the client is idle between exchanges, after the first response was read.
#eval do
  let mut m : Machine .sending := ({ config := {} } : Machine .sending).send request |>.userClosedBody
  let (m1, out, body, heads) := settle (m.feed ok1.toUTF8) .empty .empty #[]
  check (m1.isWaitingMessage && m1.error.isNone) s!"the first exchange should end cleanly: {repr m1.error}"
  let (m2, out, _, heads) := settle (m1.feed ok2.toUTF8) out body heads
  let (m3, out, _, _) := settle (m2.send request |>.userClosedBody) out .empty heads
  check (m3.error == some Error.badMessage && m3.halted)
    s!"bytes fed while idle: expected a failure, got {repr m3.error}, halted {m3.halted}"
  check (((String.fromUTF8! out).splitOn "GET /").length == 2)
    s!"no second request may be written: {(String.fromUTF8! out).quote}"
