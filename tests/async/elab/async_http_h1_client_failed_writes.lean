import Std.Http

open Std Http
open Std.Http.Protocol.H1

/-!
Tests that a client machine that failed writes nothing more. A POST whose body is still open with no
length holds its head; a malformed response or the end of input then fails the machine, and the head
must not go out, or a request that failed before it was sent would reach the server (and run twice on
a retry). A body that is streaming stops at the failure. Every malformed response is fed whole, as
every 2-read split and as every prefix. A valid early response is the control: it does not stop the
body.
-/

def check (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw (IO.userError msg)

def post : Request.Head :=
  { method := .post, version := .v11, uri := RequestTarget.originForm! "/",
    headers := Headers.empty.insert! "Host" "a" }

/-- Runs the machine until it stops making progress, collecting its output. -/
def settle (m : Machine .sending) (out : ByteArray) : Machine .sending × ByteArray := Id.run do
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

def feedAll (m : Machine .sending) (parts : List ByteArray) : Machine .sending × ByteArray :=
  parts.foldl (fun (m, out) p => settle (m.feed p) out) (m, .empty)

/-- A client that sent a POST whose body is open with no length and no data: its head is held. -/
def held : Machine .sending :=
  (settle (({ config := {} } : Machine .sending).send post) .empty).1

/-- A client whose POST is streaming a chunked body: the head and `ab` are written. -/
def streaming : Machine .sending :=
  (settle (held.sendData #[Chunk.ofByteArray "ab".toUTF8]) .empty).1

def splits (b : ByteArray) : List (List ByteArray) :=
  [b] :: (List.range (b.size - 1)).map fun i => [b.extract 0 (i + 1), b.extract (i + 1) b.size]

def prefixes (b : ByteArray) : List (List ByteArray) :=
  (List.range b.size).map fun i => [b.extract 0 (i + 1)]

/-- After `parts`, a failed machine wrote nothing, and writes nothing for more body or its end. The
whole input must fail it. -/
def failsSilently (name : String) (start : Machine .sending) (response : String) : IO Unit := do
  let bytes := response.toUTF8
  for parts in splits bytes ++ prefixes bytes do
    let (m, out) := feedAll start parts
    if parts.length == 2 || parts.head? == some bytes then
      check m.failed s!"{name}, {parts.length} read(s): expected a failure"
    if m.failed then
      check out.isEmpty s!"{name}, {parts.length} read(s): wrote {String.fromUTF8! out |>.quote} after failing"
      let (_, more) := settle (m.sendData #[Chunk.ofByteArray "more".toUTF8] |>.userClosedBody) .empty
      check more.isEmpty s!"{name}, {parts.length} read(s): wrote {String.fromUTF8! more |>.quote} for body sent after failing"

def runCases (cases : List (IO Unit)) : IO Unit := do
  let mut errors : Array String := #[]
  for c in cases do
    try c catch e => errors := errors.push (toString e)
  unless errors.isEmpty do throw (IO.userError ("\n".intercalate errors.toList))

def checkHeldIsHeld : IO Unit := do
  let (_, out) := settle (({ config := {} } : Machine .sending).send post) .empty
  check out.isEmpty s!"the held head was written: {String.fromUTF8! out |>.quote}"
  let (_, out) := settle (held.sendData #[Chunk.ofByteArray "ab".toUTF8]) .empty
  check ((String.fromUTF8! out).startsWith "POST / HTTP/1.1\r\n" && (String.fromUTF8! out).endsWith "2\r\nab\r\n")
    s!"the streaming body was not written: {String.fromUTF8! out |>.quote}"

def checkEof : IO Unit := do
  let (m, out) := settle held.noMoreInput .empty
  check m.failed s!"end of input with the request outstanding: expected a failure"
  check out.isEmpty s!"end of input: wrote {String.fromUTF8! out |>.quote} after failing"

/-- Control: a valid response while the body streams does not fail the machine, and the body goes on. -/
def checkValidEarlyResponse : IO Unit := do
  let (m, _) := feedAll streaming ["HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n".toUTF8]
  check (!m.failed) s!"a valid response failed the machine: {repr m.error}"
  let (_, out) := settle (m.sendData #[Chunk.ofByteArray "cd".toUTF8] |>.userClosedBody) .empty
  check ((String.fromUTF8! out) == "2\r\ncd\r\n0\r\n\r\n")
    s!"the body stopped after a valid response: {String.fromUTF8! out |>.quote}"

#eval runCases [
  checkHeldIsHeld,
  failsSilently "held head, bad status line" held "garbage\r\n",
  failsSilently "held head, bad Content-Length" held "HTTP/1.1 200 OK\r\nContent-Length: x\r\n\r\n",
  failsSilently "held head, bad version" held "HTTP/2.0 200 OK\r\n\r\n",
  checkEof,
  failsSilently "streaming body, bad Content-Length" streaming "HTTP/1.1 200 OK\r\nContent-Length: x\r\n\r\n",
  failsSilently "streaming body, bad chunk size" streaming
    "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\nzz\r\n",
  checkValidEarlyResponse]
