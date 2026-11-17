import Std.Http

open Std Http
open Std.Http.Protocol.H1

/-!
Tests the head of an interim (1xx) response that a server writes with `Machine.send`. Like a final
response, it says HTTP/1.1 whatever version the given head has: a server must not send a version it
does not conform to (RFC 9110 §6.2), and a client fails on `HTTP/2.0 103`. A `close` in its
`Connection` field ends the connection after the final response, as it does on a final head: a server
that sends `close` must not process further requests (RFC 9112 §9.6). The requests reach the server
in every 2-read split, and a client reads the server's output in every 2-read split.
-/

def check (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw (IO.userError msg)

/-- Runs the machine until it stops making progress, collecting its output and body. -/
def settle (m : Machine dir) (out body : ByteArray) (heads : Nat) :
    Machine dir × ByteArray × ByteArray × Nat := Id.run do
  let mut m := m
  let mut out := out
  let mut body := body
  let mut heads := heads
  for _ in [0:8] do
    let (m', r) := m.step
    m := m'
    out := out ++ r.output.toByteArray
    for e in r.events do
      if e matches .endHeaders _ then heads := heads + 1
    while m.canPullBody do
      let (m', chunk?) := m.pullBody
      m := m'
      match chunk? with
      | some c => body := body ++ c.chunk.data
      | none => break
  (m, out, body, heads)

def requests : String := "GET / HTTP/1.1\r\nHost: a\r\n\r\nGET /2 HTTP/1.1\r\nHost: a\r\n\r\n"

/-- A server that answers the first request with `interim` and then `200` with content `hi`, and
leaves the second unanswered. Returns its output and how many request heads it read. -/
def serve (parts : List ByteArray) (interim : Response.Head) : ByteArray × Nat := Id.run do
  let mut m : Machine .receiving := { config := {} }
  let mut out := ByteArray.empty
  let mut heads := 0
  let mut answered := false
  for p in parts do
    (m, out, _, heads) := settle (m.feed p) out .empty heads
    if !answered && m.isWaitingMessage then
      answered := true
      m := m.send interim
      m := m.send { status := .ok } |>.setKnownSize (.fixed 2)
        |>.sendData #[Chunk.ofByteArray "hi".toUTF8] |>.userClosedBody
      (m, out, _, heads) := settle m out .empty heads
  (out, heads)

/-- A client that sent a GET reads `parts`. Returns its error, the body and its keep-alive. -/
def read (parts : List ByteArray) : Option Error × ByteArray × Bool := Id.run do
  let mut m : Machine .sending := ({ config := {} } : Machine .sending).send
    { method := .get, version := .v11, uri := RequestTarget.originForm! "/",
      headers := Headers.empty.insert! "Host" "a" } |>.userClosedBody
  let mut body := ByteArray.empty
  for p in parts do
    (m, _, body, _) := settle (m.feed p) .empty body 0
  (m.error, body, m.keepAlive)

def splits (b : ByteArray) : List (List ByteArray) :=
  [b] :: (List.range (b.size - 1)).map fun i => [b.extract 0 (i + 1), b.extract (i + 1) b.size]

/-- The server writes `status` (HTTP/1.1) for `interim`; it reads both requests only if
`keepAlive`, and its last head says `Connection: close` otherwise. A client reads `hi` with the same
keep-alive, in every split. -/
def interimCase (name : String) (interim : Response.Head) (status : String) (keepAlive : Bool) :
    IO Unit := do
  let mut first : Option ByteArray := none
  for parts in splits requests.toUTF8 do
    let (out, heads) := serve parts interim
    let text := String.fromUTF8! out
    check (text.startsWith s!"HTTP/1.1 {status}\r\n")
      s!"{name}, {parts.length} read(s): expected an HTTP/1.1 {status} first, got {text.quote}"
    check (heads == if keepAlive then 2 else 1)
      s!"{name}, {parts.length} read(s): read {heads} request heads, keep-alive {keepAlive}"
    check (keepAlive || text.endsWith "Connection: close\r\nContent-Length: 2\r\n\r\nhi")
      s!"{name}: the final response should say close, got {text.quote}"
    if let some f := first then
      check (f == out) s!"{name}: the output depends on the read split ({parts.length} reads)"
    first := some out
  let out := first.getD .empty
  for parts in splits out do
    let (err, body, ka) := read parts
    check (err.isNone && body == "hi".toUTF8 && ka == keepAlive)
      s!"{name}, client in {parts.length} read(s): {repr err} body {String.fromUTF8! body |>.quote} keep-alive {ka}"

def runCases (cases : List (IO Unit)) : IO Unit := do
  let mut errors : Array String := #[]
  for c in cases do
    try c catch e => errors := errors.push (toString e)
  unless errors.isEmpty do throw (IO.userError ("\n".intercalate errors.toList))

def link : Headers := Headers.empty.insert! "Link" "</a>"

#eval runCases [
  interimCase "plain 103" { status := .earlyHints, headers := link } "103 Early Hints" true,
  interimCase "103 with version 1.0" { status := .earlyHints, version := .v10, headers := link }
    "103 Early Hints" true,
  interimCase "103 with version 2.0" { status := .earlyHints, version := .v20, headers := link }
    "103 Early Hints" true,
  interimCase "100 with version 3.0" { status := .«continue», version := .v30 } "100 Continue" true,
  interimCase "103 with Connection: close"
    { status := .earlyHints, headers := link.insert! "Connection" "close" } "103 Early Hints" false,
  interimCase "103 with a malformed Connection"
    { status := .earlyHints, headers := link.insert! "Connection" "\"close\"" } "103 Early Hints" false,
  interimCase "103 with Connection: keep-alive"
    { status := .earlyHints, headers := link.insert! "Connection" "keep-alive" } "103 Early Hints" true]
