import Std.Http

open Std Http
open Std.Http.Internal.Test
open Std.Http.Protocol.H1
open Std.Http.Protocol.H1.Machine

/-!
`MachineTester (dir : Direction)` is a direction-parameterized, chainable builder for exercising
`Machine dir`. Operations return a new tester; failures accumulate and are thrown as a single
`IO.userError` by `run`.

Use `MachineTester.receiving` for server-side (request parsing) tests and
`MachineTester.sending` for client-side (response parsing) tests.
-/

private structure MachineTester (dir : Direction) where

  /--
  Human-readable name used in error messages.
  -/
  name : String

  /--
  The machine under test.
  -/
  machine : Machine dir

  /--
  Events and output produced by the most recent `step` or `pullBody`.
  -/
  lastStep : Option (StepResult dir) := none

  /--
  Body chunks collected by `drainBody` / `pullBody`.
  -/
  pulled : Array PulledChunk := #[]

  /--
  Cumulative wire output across all `step` calls.
  -/
  allOutput : ByteArray := .empty

  /--
  Accumulated assertion failures; `run` throws if non-empty.
  -/
  errors : Array String := #[]

namespace MachineTester

private def addError (t : MachineTester dir) (msg : String) : MachineTester dir :=
  { t with errors := t.errors.push s!"[{t.name}] {msg}" }

private def withLastStep
    (t : MachineTester dir) (ctx : String)
    (k : MachineTester dir → StepResult dir → MachineTester dir) : MachineTester dir :=
  match t.lastStep with
  | none => t.addError s!"{ctx}: no step result (call .step first)"
  | some step => k t step

/-- Create a new tester for the given direction. -/
def new (name : String) (config : Protocol.H1.Config := {}) : MachineTester dir :=
  { name, machine := { config } }

/-- Create a new server-side tester (receives requests, sends responses). -/
def receiving (name : String) (config : Protocol.H1.Config := {}) : MachineTester .receiving :=
  { name, machine := { config } }

/-- Create a new client-side tester (sends requests, receives responses). -/
def sending (name : String) (config : Protocol.H1.Config := {}) : MachineTester .sending :=
  { name, machine := { config } }

/-- Feed a UTF-8 string to the machine. -/
def feed (t : MachineTester dir) (data : String) : MachineTester dir :=
  { t with machine := t.machine.feed data.toUTF8, lastStep := none }

/-- Feed raw bytes to the machine. -/
def feedBytes (t : MachineTester dir) (data : ByteArray) : MachineTester dir :=
  { t with machine := t.machine.feed data, lastStep := none }

/-- Run one step of the state machine and record the result. -/
def step (t : MachineTester dir) : MachineTester dir :=
  let (machine, stepResult) := t.machine.step
  let allOutput := t.allOutput ++ stepResult.output.toByteArray
  { t with machine, lastStep := some stepResult, allOutput }


def debug (t : MachineTester dir) : MachineTester dir :=
  dbg_trace "resp: {repr <| t.lastStep.map (StepResult.events)}";
  t

/--
Pull at most one body chunk. Updates `pulled` and replaces `lastStep` with the
events emitted during the pull.
-/
def pullBody (t : MachineTester dir) : MachineTester dir :=
  let (machine, chunk?) := t.machine.pullBody
  let (machine, pullEvents) := machine.takeEvents
  let pulled := match chunk? with
    | some chunk => t.pulled.push chunk
    | none => t.pulled
  { t with machine, pulled, lastStep := some { events := pullEvents } }

/--
Drain all immediately-available body chunks.

The loop exits when `canPullBodyNow` becomes false (either the body is complete
or the machine stalls waiting for more data). The stall flag is set internally
by `pullBody`, so no explicit `remainingBytes` guard is needed.
-/
def drainBody (t : MachineTester dir) (fuel : Nat := 4096) : MachineTester dir := Id.run do
  let mut t := t
  let mut remaining := fuel
  while remaining > 0 && t.machine.canPullBodyNow do
    remaining := remaining - 1
    t := t.pullBody
  t

/-- Set the known outgoing body size (forwarded to the writer). -/
def setKnownSize (t : MachineTester dir) (size : Body.Length) : MachineTester dir :=
  { t with machine := t.machine.setKnownSize size }

/-- Signal EOF on the reader input (no more socket bytes will arrive). -/
def noMoreInput (t : MachineTester dir) : MachineTester dir :=
  { t with machine := t.machine.noMoreInput }

/-- Send a message head (request for `.sending`, response for `.receiving`). -/
def send (t : MachineTester dir) (head : Message.Head dir.swap) : MachineTester dir :=
  { t with machine := t.machine.send head }

/-- Signal that the application has finished writing the message body. -/
def userClosedBody (t : MachineTester dir) : MachineTester dir :=
  { t with machine := t.machine.userClosedBody }

/-- Resolve an `Expect: 100-continue` decision. No-op for `.sending` direction. -/
def canContinue (t : MachineTester dir) (status : Status) : MachineTester dir :=
  { t with machine := t.machine.canContinue status }

/-- Send an error response with `Connection: close` and shut down input. Only valid for `.receiving`. -/
def closeWithError (t : MachineTester .receiving) (status : Status) : MachineTester .receiving :=
  { t with machine := t.machine.closeWithError status }

/-- Enqueue body chunks into the writer buffer. -/
def sendData (t : MachineTester dir) (chunks : Array Chunk) : MachineTester dir :=
  { t with machine := t.machine.sendData chunks }

/-- Enqueue raw bytes as a single body chunk into the writer buffer. -/
def sendBytes (t : MachineTester dir) (data : ByteArray) : MachineTester dir :=
  t.sendData #[{ data, extensions := #[] }]

/-- Assert a predicate on the current machine. -/
def assert (t : MachineTester dir) (pred : Machine dir → Bool) (msg : String) : MachineTester dir :=
  if pred t.machine then t else t.addError msg

/--
Assert that the machine has not failed (reader state ≠ `.failed`).

**Note:** `machine.failed` returns `false` after any `step` call because `step` transitions
the reader from `.failed` to `.closed`. Use `assertNoError` for post-step success checks.
-/
def assertNoFailure (t : MachineTester dir) : MachineTester dir :=
  t.assert (fun m => !m.failed)
    s!"machine should not fail, got error: {repr t.machine.error}"

/-- Assert that `machine.error` is `none`. -/
def assertNoError (t : MachineTester dir) : MachineTester dir :=
  t.assert (fun m => m.error == none)
    s!"machine should have no error, got: {repr t.machine.error}"

/-- Assert that the machine has failed with the given error. -/
def assertFailedWith (t : MachineTester dir) (expected : Error) : MachineTester dir :=
  t.assert (fun m => m.error == some expected)
    s!"expected error {repr expected}, got {repr t.machine.error}"

/-- Assert that `canPullBody` is true. -/
def assertCanPullBody (t : MachineTester dir) : MachineTester dir :=
  t.assert (·.canPullBody) "expected canPullBody = true"

/-- Assert that `canPullBodyNow` is true. -/
def assertCanPullBodyNow (t : MachineTester dir) : MachineTester dir :=
  t.assert (·.canPullBodyNow) "expected canPullBodyNow = true"

/-- Assert that the reader is in the `complete` state. -/
def assertReaderComplete (t : MachineTester dir) : MachineTester dir :=
  t.assert (·.isReaderComplete)
    s!"expected reader to be complete, state: {repr t.machine.reader.state}"

/-- Assert that the reader is in the `closed` state. -/
def assertReaderClosed (t : MachineTester dir) : MachineTester dir :=
  t.assert (·.isReaderClosed)
    s!"expected reader to be closed, state: {repr t.machine.reader.state}"

/-- Assert that `keepAlive` is true on the machine. -/
def assertKeepAlive (t : MachineTester dir) : MachineTester dir :=
  t.assert (·.keepAlive) "expected keepAlive = true"

/-- Assert that `keepAlive` is false on the machine. -/
def assertNotKeepAlive (t : MachineTester dir) : MachineTester dir :=
  t.assert (fun m => !m.keepAlive) "expected keepAlive = false"

/-- Assert that `isWaitingMessage` is true (writer in `waitingHeaders`, `!sentMessage`). -/
def assertIsWaitingMessage (t : MachineTester dir) : MachineTester dir :=
  t.assert (·.isWaitingMessage) "expected isWaitingMessage = true"

/-- Assert that `halted` is true (both reader and writer closed, no output). -/
def assertHalted (t : MachineTester dir) : MachineTester dir :=
  t.assert (·.halted) "expected machine to be halted"

/-- Assert that at least one event in the last step matches `pred`. -/
def assertHasEvent
    (t : MachineTester dir) (pred : Event dir → Bool) (msg : String) : MachineTester dir :=
  t.withLastStep "assertHasEvent" fun t step =>
    if step.events.any pred then t
    else t.addError s!"{msg}\n  events: {repr step.events}"

/-- Assert that no event in the last step matches `pred`. -/
def assertNoEvent
    (t : MachineTester dir) (pred : Event dir → Bool) (msg : String) : MachineTester dir :=
  t.withLastStep "assertNoEvent" fun t step =>
    if step.events.any pred then
      t.addError s!"{msg}\n  events: {repr step.events}"
    else t

/-- Assert that the last step contains an `endHeaders` event. -/
def assertHasEndHeaders (t : MachineTester dir) : MachineTester dir :=
  t.assertHasEvent (fun | .endHeaders _ => true | _ => false) "expected endHeaders event"

/-- Assert that the last step contains a `failed` event for the given error. -/
def assertHasFailedEvent (t : MachineTester dir) (expected : Error) : MachineTester dir :=
  t.assertHasEvent (fun | .failed err => err == expected | _ => false)
    s!"expected failed event with {repr expected}"

/-- Assert that the last step contains a `closeBody` event. -/
def assertHasCloseBody (t : MachineTester dir) : MachineTester dir :=
  t.assertHasEvent (fun | .closeBody => true | _ => false) "expected closeBody event"

/-- Assert that the last step contains a `next` event. -/
def assertHasNext (t : MachineTester dir) : MachineTester dir :=
  t.assertHasEvent (fun | .next => true | _ => false) "expected next event"

/-- Assert that the last step contains a `continue` event. -/
def assertHasContinue (t : MachineTester dir) : MachineTester dir :=
  t.assertHasEvent (fun | .«continue» => true | _ => false) "expected continue event"

/-- Inspect the `endHeaders` payload in the last step. -/
def onEndHeaders
    (t : MachineTester dir)
    (f : MachineTester dir → Message.Head dir → MachineTester dir) : MachineTester dir :=
  t.withLastStep "onEndHeaders" fun t step =>
    match step.events.findSome? (fun | .endHeaders h => some h | _ => none) with
    | none => t.addError "onEndHeaders: no endHeaders event in last step"
    | some head => f t head

/-- Assert that the cumulative output starts with the given ASCII string. -/
def assertOutputStartsWith (t : MachineTester dir) (pfx : String) (msg : String) : MachineTester dir :=
  let s := String.fromUTF8! t.allOutput
  if s.startsWith pfx then t
  else
    let preview := String.fromUTF8! (t.allOutput.extract 0 (min t.allOutput.size 120))
    t.addError s!"{msg}: expected output to start with {repr pfx}\n  got: {repr preview}"

/-- Assert that the cumulative output contains the given ASCII substring. -/
def assertOutputContains (t : MachineTester dir) (needle : String) (msg : String) : MachineTester dir :=
  let haystack := t.allOutput
  let nb := needle.toUTF8
  let found :=
    if nb.isEmpty then true
    else if nb.size > haystack.size then false
    else (Array.range (haystack.size - nb.size + 1)).any fun i =>
      (Array.range nb.size).all fun j => haystack.get! (i + j) == nb.get! j
  if found then t
  else
    let preview := String.fromUTF8! (haystack.extract 0 (min haystack.size 160))
    t.addError s!"{msg}: expected output to contain {repr needle}\n  output: {repr preview}"

/-- Assert that the cumulative output does not contain the given ASCII substring. -/
def assertOutputNotContains (t : MachineTester dir) (needle : String) (msg : String) : MachineTester dir :=
  let haystack := t.allOutput
  let nb := needle.toUTF8
  let found :=
    if nb.isEmpty then true
    else if nb.size > haystack.size then false
    else (Array.range (haystack.size - nb.size + 1)).any fun i =>
      (Array.range nb.size).all fun j => haystack.get! (i + j) == nb.get! j
  if found then
    let preview := String.fromUTF8! (haystack.extract 0 (min haystack.size 160))
    t.addError s!"{msg}: expected output NOT to contain {repr needle}\n  output: {repr preview}"
  else t

/-- Assert that the total bytes pulled so far equal `expected`. -/
def assertPulledBody (t : MachineTester dir) (expected : ByteArray) : MachineTester dir :=
  let got := t.pulled.foldl (fun acc c => acc ++ c.chunk.data) ByteArray.empty
  if got == expected then t
  else t.addError
    s!"body mismatch:\n  expected={String.fromUTF8! expected |>.quote}\n  got={String.fromUTF8! got |>.quote}"

/-- Assert that at least one chunk was pulled and the last one is `final`. -/
def assertLastChunkFinal (t : MachineTester dir) : MachineTester dir :=
  match t.pulled.back? with
  | none => t.addError "assertLastChunkFinal: no chunks pulled yet"
  | some chunk =>
    if chunk.final then t
    else t.addError "expected last pulled chunk to be final"

/-- Run a custom check on the current machine state. -/
def onMachine (t : MachineTester dir) (f : MachineTester dir → Machine dir → MachineTester dir) : MachineTester dir :=
  f t t.machine

/-- Throw if any assertion has failed; otherwise succeed. -/
def run (t : MachineTester dir) : IO Unit :=
  unless t.errors.isEmpty do
    throw <| IO.userError <| "\n".intercalate t.errors.toList

end MachineTester

----------------------------------------------------------------------------------------------------

private def mkGet10 (path : String := "/") : String :=
  s!"GET {path} HTTP/1.0\r\n\r\n"

private def mkPostHead (path : String) (bodyLen : Nat) (extra : String := "") : String :=
  s!"POST {path} HTTP/1.1\r\nHost: example.com\r\nContent-Length: {bodyLen}\r\n{extra}\r\n"

private def mkChunkedPost (path : String) (extra : String := "") : String :=
  s!"POST {path} HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: chunked\r\n{extra}\r\n"

----------------------------------------------------------------------------------------------------

private def minimalGetRequest : Request.Head :=
  { method := .get, version := .v11, uri := RequestTarget.originForm! "/",
    headers := Headers.empty.insert! "Host" "example.com" }

----------------------------------------------------------------------------------------------------

#eval runGroup "RFC 9112 §2.2: leading CRLF before request-line" do
  MachineTester.receiving "§2.2: leading CRLF ignored" (config := { maxLeadingEmptyLines := 8 })
    |>.feed "\r\n\r\nGET / HTTP/1.1\r\nHost: example.com\r\n\r\n"
    |>.step |>.assertNoError |>.assertHasEndHeaders |>.run

  MachineTester.receiving "§2.2: maximum leading CRLFs" (config := { maxLeadingEmptyLines := 2 })
    |>.feed "\r\n\r\n\r\nGET / HTTP/1.1\r\nHost: example.com\r\n\r\n"
    |>.step |>.assertFailedWith .badMessage |>.run

#eval runGroup "RFC 9112 §2–§3: version and method parsing" do
  MachineTester.receiving "§2: HTTP/2.0 → unsupportedVersion"
    |>.feed "GET / HTTP/2.0\r\nHost: example.com\r\n\r\n"
    |>.step |>.assertFailedWith .unsupportedVersion |>.run

  MachineTester.receiving "§3: unrecognized method → badMessage"
    |>.feed "LEAN / HTTP/1.1\r\nHost: example.com\r\n\r\n"
    |>.step |>.assertFailedWith .badMessage |>.run

  MachineTester.receiving "§3: GET method and HTTP/1.1 version parsed correctly"
    |>.feed "GET /path HTTP/1.1\r\nHost: example.com\r\n\r\n"
    |>.step |>.assertNoError
    |>.onEndHeaders (fun t head =>
      if head.method != .get then t.addError s!"expected method GET, got {repr head.method}"
      else if head.version != .v11 then t.addError s!"expected HTTP/1.1, got {repr head.version}"
      else t)
    |>.run

#eval runGroup "RFC 9112 §3.2–§3.3: request-target form and Host" do
  MachineTester.receiving "§3.2.1: origin-form path preserved"
    |>.feed "GET /api/v1/users?active=true HTTP/1.1\r\nHost: api.example.com\r\n\r\n"
    |>.step |>.assertNoError
    |>.onEndHeaders (fun t head =>
      let path := toString head.uri.path
      if path != "/api/v1/users" then t.addError s!"expected path /api/v1/users, got {path}"
      else t)
    |>.run

  MachineTester.receiving "§3.2: non-OPTIONS asterisk-form → badMessage"
    |>.feed "GET * HTTP/1.1\r\nHost: example.com\r\n\r\n"
    |>.step |>.assertFailedWith .badMessage |>.run

  MachineTester.receiving "§3.2: non-CONNECT authority-form → badMessage"
    |>.feed "GET example.com:80 HTTP/1.1\r\nHost: example.com\r\n\r\n"
    |>.step |>.assertFailedWith .badMessage |>.run

  MachineTester.receiving "§3.2: origin-form valid for GET"
    |>.feed "GET /ata HTTP/1.1\r\nHost: example.com\r\n\r\n"
    |>.step |>.assertNoError |>.run

  MachineTester.receiving "§3.3: absolute-form with explicit :80"
    |>.feed "GET http://example.com:80/path HTTP/1.1\r\nHost: example.com\r\n\r\n"
    |>.step |>.assertNoError |>.assertHasEndHeaders |>.run

  MachineTester.receiving "§3.2: HTTP/1.1 missing Host → badMessage"
    |>.feed "GET / HTTP/1.1\r\n\r\n"
    |>.step |>.assertFailedWith .badMessage |>.run

  MachineTester.receiving "§3.2: HTTP/1.1 duplicate Host → badMessage"
    |>.feed "GET / HTTP/1.1\r\nHost: a.com\r\nHost: b.com\r\n\r\n"
    |>.step |>.assertFailedWith .badMessage |>.run

  -- RFC 9112 §3.2.2: Host is left as-is; authority is available via the URI.
  MachineTester.receiving "§3.2: absolute-form Host preserved, authority in URI"
    |>.feed "GET http://example.com:80/path HTTP/1.1\r\nHost: random.com\r\n\r\n"
    |>.step |>.assertNoError
    |>.onEndHeaders (fun t head =>
      let t := match head.headers.get? .host with
        | some v => if v.value == "random.com" then t else t.addError s!"expected Host=random.com, got {v.value.quote}"
        | none => t.addError "missing Host header"
      match head.uri.authority? with
        | some a => if toString a == "example.com:80" then t else t.addError s!"expected URI authority=example.com:80, got {toString a}"
        | none => t.addError "missing URI authority")
    |>.run

-- Any multi-TE message is rejected as a request-smuggling defence.
#eval runGroup "RFC 9112 §6: Transfer-Encoding validation" do
  MachineTester.receiving "§6.1: multiple Transfer-Encoding headers → badMessage"
    |>.feed "POST / HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: gzip\r\nTransfer-Encoding: chunked\r\n\r\n"
    |>.step |>.assertFailedWith .badMessage |>.run

  MachineTester.receiving "§6.1: Transfer-Encoding: identity → badMessage"
    |>.feed "POST / HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: identity\r\n\r\n"
    |>.step |>.assertFailedWith .badMessage |>.run

#eval runGroup "RFC 9112 §6.3: body framing" do
  MachineTester.receiving "§6.3: no CL/TE → empty body"
    |>.feed (mkGet "/")
    |>.step |>.assertNoError |>.assertHasEndHeaders
    |>.assertCanPullBodyNow |>.drainBody
    |>.assertPulledBody .empty |>.assertLastChunkFinal |>.run

  let body := "Hello, World!".toUTF8
  MachineTester.receiving "§6.3: Content-Length body delivered exactly"
    |>.feed (mkPostHead "/" body.size ++ String.fromUTF8! body)
    |>.step |>.assertNoError |>.assertHasEndHeaders
    |>.drainBody |>.assertPulledBody body |>.assertLastChunkFinal |>.run

  MachineTester.receiving "§6.3: CL + TE mixed → badMessage (request-smuggling prevention)"
    |>.feed "POST / HTTP/1.1\r\nHost: example.com\r\nContent-Length: 5\r\nTransfer-Encoding: chunked\r\n\r\n"
    |>.step |>.assertFailedWith .badMessage |>.run

  MachineTester.receiving "§6.3: multiple Content-Length → badMessage"
    |>.feed "POST / HTTP/1.1\r\nHost: example.com\r\nContent-Length: 5\r\nContent-Length: 5\r\n\r\n"
    |>.step |>.assertFailedWith .badMessage |>.run

  let respBody := "Hello!".toUTF8
  MachineTester.sending "§6.3: response Content-Length body delivered exactly"
    |>.send minimalGetRequest |>.step
    |>.feed s!"HTTP/1.1 200 OK\r\nContent-Length: {respBody.size}\r\n\r\n"
    |>.feedBytes respBody |>.step |>.assertNoError
    |>.drainBody |>.assertPulledBody respBody |>.assertLastChunkFinal |>.run

  let eofBody := "eof body".toUTF8
  MachineTester.sending "§6.3: EOF-delimited response body; keep-alive disabled"
    |>.send minimalGetRequest |>.step
    |>.feed "HTTP/1.1 200 OK\r\n\r\n"
    |>.step |>.assertNoError |>.assertNotKeepAlive
    |>.feedBytes eofBody |>.noMoreInput
    |>.drainBody |>.assertPulledBody eofBody |>.assertLastChunkFinal |>.run

  let partialBody := "hello".toUTF8
  MachineTester.receiving "§6.3: noMoreInput mid fixed-length body → connectionClosed"
    |>.feed (mkPostHead "/" 10 ++ String.fromUTF8! partialBody)
    |>.step |>.assertHasEndHeaders |>.noMoreInput
    |>.drainBody |>.assertFailedWith .connectionClosed |>.run

  MachineTester.receiving "§6.3: fixed-length body stops at declared byte count"
    |>.feed (mkPostHead "/" 5 ++ "helloworld")
    |>.step |>.assertHasEndHeaders
    |>.drainBody
    |>.assertPulledBody "hello".toUTF8
    |>.assertLastChunkFinal |>.assertNoError |>.run

  let part1 := "hel".toUTF8
  let part2 := "lo".toUTF8
  MachineTester.receiving "§6.3: fixed-length body assembled across incremental feeds"
    |>.feed (mkPostHead "/" 5) |>.step |>.assertHasEndHeaders
    |>.feedBytes part1 |>.pullBody
    |>.feedBytes part2 |>.pullBody
    |>.assertPulledBody (part1 ++ part2) |>.assertLastChunkFinal |>.run

#eval runGroup "RFC 9112 §7.1: chunked transfer encoding" do
  -- §7.1: chunks decoded to raw body bytes
  let reqBody := "helloworld".toUTF8
  MachineTester.receiving "§7.1: chunked TE decoded to raw body"
    |>.feed (mkChunkedPost "/" ++ "5\r\nhello\r\n5\r\nworld\r\n0\r\n\r\n")
    |>.step |>.assertNoError |>.assertHasEndHeaders
    |>.drainBody |>.assertPulledBody reqBody |>.assertLastChunkFinal |>.run

  -- §7.1: zero-length chunked body → empty body, final chunk
  MachineTester.receiving "§7.1: empty chunked body"
    |>.feed (mkChunkedPost "/" ++ "0\r\n\r\n")
    |>.step |>.assertNoError
    |>.drainBody |>.assertPulledBody .empty |>.assertLastChunkFinal |>.run

  -- §7.1: 200 response with chunked body decoded correctly
  let respBody := "chunked".toUTF8
  MachineTester.sending "§7.1: response chunked body decoded"
    |>.send minimalGetRequest |>.step
    |>.feed "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n7\r\nchunked\r\n0\r\n\r\n"
    |>.step |>.assertNoError
    |>.drainBody |>.assertPulledBody respBody |>.assertLastChunkFinal |>.run

  -- §7.1: EOF mid chunked body (size line received but no chunk data) → connectionClosed
  MachineTester.receiving "§7.1: noMoreInput mid chunked body → connectionClosed"
    |>.feed (mkChunkedPost "/" ++ "5\r\n")  -- chunk size line but no chunk payload
    |>.step |>.assertHasEndHeaders |>.noMoreInput
    |>.pullBody   -- tries to read 5-byte chunk data, hits EOF → connectionClosed
    |>.assertFailedWith .connectionClosed |>.run

  -- §7.1.1: chunk-extension fields preserved in PulledChunk.chunk.extensions
  let extBody := "hello".toUTF8
  MachineTester.receiving "§7.1.1: chunk extensions preserved in PulledChunk"
    |>.feed (mkChunkedPost "/" ++ "5;quality=0.9\r\nhello\r\n0\r\n\r\n")
    |>.step |>.assertHasEndHeaders
    |>.drainBody |>.assertPulledBody extBody
    |>.onMachine (fun t _ =>
      match t.pulled[0]? with
      | none => t.addError "no chunks pulled"
      | some c =>
        if c.chunk.extensions.isEmpty
          then t.addError "expected chunk extensions to be non-empty for chunk with extension"
          else t)
    |>.run

  -- §7.1: server writes chunk-size lines and terminal 0\r\n\r\n when userClosedBody is called
  let body1 := "Hello, ".toUTF8
  let body2 := "World!".toUTF8
  MachineTester.receiving "§7.1: server sends chunked response — wire encoding correct"
    |>.feed (mkGet "/") |>.step |>.assertIsWaitingMessage
    |>.send { status := .ok } |>.setKnownSize .chunked
    |>.sendBytes body1 |>.step
    |>.sendBytes body2 |>.userClosedBody |>.step
    |>.assertOutputContains "7\r\nHello, \r\n" "expected first chunk in wire output"
    |>.assertOutputContains "6\r\nWorld!\r\n" "expected second chunk in wire output"
    |>.assertOutputContains "0\r\n\r\n" "expected final empty chunk in wire output"
    |>.run

  -- §7.1: chunked body assembled when size line and data arrive in separate feeds
  let splitBody := "hello".toUTF8
  MachineTester.receiving "§7.1: chunked body assembled across incremental feeds"
    |>.feed (mkChunkedPost "/" ++ "5\r\n")
    |>.step |>.assertHasEndHeaders
    |>.pullBody
    |>.feedBytes ("hello\r\n".toUTF8)
    |>.pullBody
    |>.feed "0\r\n\r\n"
    |>.pullBody
    |>.assertPulledBody splitBody |>.assertLastChunkFinal |>.run

#eval runGroup "RFC 9112 §9.3: connection persistence" do
  -- §9.3: HTTP/1.1 connections are persistent by default
  MachineTester.receiving "§9.3: HTTP/1.1 default keep-alive = true"
    |>.feed (mkGet "/") |>.step |>.assertNoError |>.assertKeepAlive |>.run

  -- §9.3: HTTP/1.0 connections are not persistent by default
  MachineTester.receiving "§9.3: HTTP/1.0 default keep-alive = false"
    |>.feed (mkGet10 "/") |>.step |>.assertNoError |>.assertNotKeepAlive |>.run

  -- §9.3: explicit (redundant) Connection: keep-alive MUST NOT suppress default keep-alive
  MachineTester.receiving "§9.3: HTTP/1.1 explicit Connection:keep-alive → keepAlive = true"
    |>.feed "GET / HTTP/1.1\r\nHost: example.com\r\nConnection: keep-alive\r\n\r\n"
    |>.step |>.assertNoError |>.assertKeepAlive |>.run

  -- §9.3: after completing first request, machine resets and parses second (pipelining)
  let req1 := mkGet "/"
  let req2 := mkGet "/second"
  MachineTester.receiving "§9.3: pipelining — two requests on one connection"
    |>.feed (req1 ++ req2) |>.step |>.assertHasEndHeaders |>.assertKeepAlive
    |>.send { status := .ok } |>.setKnownSize (.fixed 0) |>.userClosedBody
    |>.drainBody |>.step |>.assertHasNext
    |>.step |>.assertHasEndHeaders |>.run

  -- §9.3: pipelining after CL:0 body — second request parses correctly
  let post1 := "POST /a HTTP/1.1\r\nHost: example.com\r\nContent-Length: 0\r\n\r\n"
  let get2  := "GET /b HTTP/1.1\r\nHost: example.com\r\n\r\n"
  MachineTester.receiving "§9.3: pipelining after CL:0 body — second request path correct"
    |>.feed (post1 ++ get2) |>.step |>.assertHasEndHeaders
    |>.drainBody |>.assertPulledBody .empty
    |>.send { status := .ok } |>.setKnownSize (.fixed 0) |>.userClosedBody
    |>.step |>.assertHasNext
    |>.step |>.assertHasEndHeaders
    |>.onEndHeaders (fun t head =>
      let path := toString head.uri.path
      if path == "/b" then t
      else t.addError s!"expected second request path /b, got {path}")
    |>.run

  -- §9.3: resetForNextMessage must preserve the noMoreInput flag so the machine
  --       halts after the pipeline is exhausted and the socket has closed
  let req1 := mkGet "/first"
  let req2 := mkGet "/second"
  MachineTester.receiving "§9.3: resetForNextMessage preserves noMoreInput after pipeline exhausted"
    |>.feed (req1 ++ req2) |>.noMoreInput
    |>.step |>.assertHasEndHeaders
    |>.send { status := .ok } |>.setKnownSize (.fixed 0) |>.userClosedBody
    |>.drainBody |>.step |>.assertHasNext
    |>.step |>.assertHasEndHeaders
    |>.send { status := .ok } |>.setKnownSize (.fixed 0) |>.userClosedBody
    |>.drainBody |>.step
    |>.assertHasEvent (fun | .close => true | _ => false)
        "expected .close after pipeline exhausted on closed socket"
    |>.step |>.assertHalted |>.run

#eval runGroup "RFC 9112 §9.6: connection close" do
  -- §9.6: Connection: close in request → keep-alive = false
  MachineTester.receiving "§9.6: HTTP/1.1 Connection:close → keep-alive = false"
    |>.feed "GET / HTTP/1.1\r\nHost: example.com\r\nConnection: close\r\n\r\n"
    |>.step |>.assertNoError |>.assertNotKeepAlive |>.run

  -- §9.6: Connection: close injected into response when keep-alive is false
  MachineTester.receiving "§9.6: Connection:close injected into response when not keep-alive"
    |>.feed "GET / HTTP/1.1\r\nHost: example.com\r\nConnection: close\r\n\r\n"
    |>.step |>.assertNotKeepAlive
    |>.send { status := .ok } |>.setKnownSize (.fixed 0) |>.userClosedBody |>.step
    |>.assertOutputContains "Connection: close" "expected Connection: close in response" |>.run

  -- §9.6: HTTP/1.1 response with Connection: close → keep-alive disabled
  MachineTester.sending "§9.6: HTTP/1.1 response Connection:close → keep-alive = false"
    |>.send minimalGetRequest |>.step
    |>.feed "HTTP/1.1 200 OK\r\nConnection: close\r\nContent-Length: 0\r\n\r\n"
    |>.step |>.assertNoError |>.assertNotKeepAlive |>.run

#eval runGroup "RFC 9110 §6–§7: header handling" do
  -- §6.3: custom application headers are preserved in the parsed head
  MachineTester.receiving "§6.3: custom headers preserved"
    |>.feed "GET / HTTP/1.1\r\nHost: example.com\r\nX-Custom: my-value\r\nAuthorization: Bearer tok\r\n\r\n"
    |>.step |>.assertNoError
    |>.onEndHeaders (fun t head =>
      let custom := (head.headers.get? (.ofString! "X-Custom")).map (·.value)
      if custom != some "my-value" then t.addError s!"X-Custom mismatch: {repr custom}"
      else t)
    |>.run

  -- §7.2: empty Host header is valid for origin-form in HTTP/1.1
  MachineTester.receiving "§7.2: HTTP/1.1 empty Host valid for origin-form"
    |>.feed "GET / HTTP/1.1\r\nHost: \r\n\r\n"
    |>.step |>.assertNoError |>.assertHasEndHeaders |>.run

#eval runGroup "RFC 9110 §15.5.14: Expect: 100-continue" do
  -- accepted: body becomes readable after canContinue .continue
  let body := "hello".toUTF8
  MachineTester.receiving "§15.5.14: Expect:100-continue accepted → body readable"
    |>.feed (mkPostHead "/upload" body.size "Expect: 100-continue\r\n")
    |>.step |>.assertHasEndHeaders |>.assertHasContinue
    |>.canContinue .«continue»
    |>.feedBytes body |>.step |>.assertCanPullBodyNow
    |>.drainBody |>.assertPulledBody body |>.run

  -- rejected: reader closed, body not delivered
  MachineTester.receiving "§15.5.14: Expect:100-continue rejected → reader closed"
    |>.feed (mkPostHead "/upload" 5 "Expect: 100-continue\r\n")
    |>.step |>.assertHasContinue
    |>.canContinue .expectationFailed
    |>.assertReaderClosed
    |>.assert (fun m => !m.canPullBody) "body must not be pullable after rejection" |>.run

  -- CL:0 + Expect:100-continue → empty body after acceptance
  MachineTester.receiving "§10.1.1: Expect:100-continue + Content-Length:0 → empty body after acceptance"
    |>.feed "POST / HTTP/1.1\r\nHost: example.com\r\nContent-Length: 0\r\nExpect: 100-continue\r\n\r\n"
    |>.step |>.assertHasEndHeaders |>.assertHasContinue
    |>.canContinue .«continue»
    |>.pullBody |>.assertPulledBody .empty |>.assertLastChunkFinal |>.run

  -- §15.5.14: writer completing a non-1xx response while reader is in .continue state
  --           must force-close the reader (body will never arrive after rejection)
  MachineTester.receiving "§15.5.14: non-final send while reader awaits canContinue → .close emitted"
    |>.feed (mkPostHead "/upload" 5 "Expect: 100-continue\r\n")
    |>.step |>.assertHasContinue
    |>.send { status := .expectationFailed } |>.setKnownSize (.fixed 0) |>.userClosedBody
    |>.step
    |>.assertHasEvent (fun | .close => true | _ => false)
        "expected .close: writer completed after rejecting Expect: 100-continue, body will never arrive"
    |>.run

#eval runGroup "RFC 9110 §15.2: informational responses" do
  -- §15.2: multiple 1xx responses before the real response are all skipped
  MachineTester.sending "§15.2: multiple 1xx responses all skipped"
    |>.send minimalGetRequest |>.step
    |>.feed "HTTP/1.1 100 Continue\r\n\r\n" |>.step
    |>.feed "HTTP/1.1 102 Processing\r\n\r\n" |>.step
    |>.feed "HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n" |>.step
    |>.assertNoError
    |>.onEndHeaders (fun t head =>
      if head.status != .ok then
        t.addError s!"expected 200 OK after 1xx chain, got {repr head.status}"
      else t)
    |>.run

  -- §15.2: 1xx responses are valid while awaiting canContinue; writer must remain open
  MachineTester.receiving "§15.2: 1xx interim response while reader awaits canContinue → writer stays open"
    |>.feed (mkPostHead "/upload" 5 "Expect: 100-continue\r\n")
    |>.step |>.assertHasContinue
    |>.send { status := .processing } |>.step
    |>.assertIsWaitingMessage |>.run

#eval runGroup "RFC 7231 §4.3.2: HEAD request handling" do
  -- body bytes suppressed; Content-Length metadata still emitted so client knows size
  let body := "hello".toUTF8
  MachineTester.receiving "§4.3.2: HEAD response — body bytes suppressed, Content-Length preserved"
    |>.feed "HEAD / HTTP/1.1\r\nHost: example.com\r\n\r\n"
    |>.step |>.assertIsWaitingMessage
    |>.send { status := .ok, headers := Headers.empty.insert! "Content-Length" "5" }
    |>.sendBytes body |>.userClosedBody |>.step |>.step
    |>.assertOutputContains "HTTP/1.1 200" "expected 200 OK status line"
    |>.assertOutputContains "Content-Length: 5" "expected Content-Length metadata preserved"
    |>.assertOutputNotContains "hello" "HEAD response must not contain body bytes on the wire"
    |>.run

#eval runGroup "RFC 2616: HTTP/1.0 compatibility" do
  -- RFC 2068 §19.4.6: HTTP/1.0 does not define chunked transfer encoding
  MachineTester.receiving "§19.4.6: chunked TE on HTTP/1.0 → badMessage"
    |>.feed "POST / HTTP/1.0\r\nTransfer-Encoding: chunked\r\n\r\n"
    |>.step |>.assertFailedWith .badMessage |>.run

  -- RFC 2616 §8.1: HTTP/1.0 does not default to persistent connections
  MachineTester.sending "§8.1: client receives HTTP/1.0 response → keepAlive = false"
    |>.send minimalGetRequest |>.step
    |>.feed "HTTP/1.0 200 OK\r\nContent-Length: 0\r\n\r\n"
    |>.step |>.assertNoError |>.assertNotKeepAlive |>.run

  -- RFC 2616 §14.23: Host header is optional in HTTP/1.0
  MachineTester.receiving "§14.23: HTTP/1.0 without Host → valid"
    |>.feed "GET / HTTP/1.0\r\n\r\n"
    |>.step |>.assertNoError |>.assertHasEndHeaders |>.run

  MachineTester.receiving "§14.23: HTTP/1.0 single Host → valid"
    |>.feed "GET / HTTP/1.0\r\nHost: example.com\r\n\r\n"
    |>.step |>.assertNoError |>.assertHasEndHeaders |>.run

  MachineTester.receiving "§14.23: HTTP/1.0 duplicate Host → badMessage (To avoid exploits)"
    |>.feed "GET / HTTP/1.0\r\nHost: a.com\r\nHost: b.com\r\n\r\n"
    |>.step |>.assertFailedWith .badMessage |>.run

  -- RFC 2616 §19.7.1: HTTP/1.0 + Connection: keep-alive → keep-alive enabled
  MachineTester.receiving "§19.7.1: HTTP/1.0 Connection:keep-alive → keep-alive = true"
    |>.feed "GET / HTTP/1.0\r\nConnection: keep-alive\r\n\r\n"
    |>.step |>.assertNoError |>.assertKeepAlive |>.run

  -- §19.7.1: HTTP/1.0 keep-alive allows a second request on the same connection
  let http10req1 := "GET / HTTP/1.0\r\nConnection: keep-alive\r\n\r\n"
  let http10req2 := "GET /second HTTP/1.0\r\n\r\n"
  MachineTester.receiving "§19.7.1: HTTP/1.0 keep-alive pipelining — second request parsed"
    |>.feed (http10req1 ++ http10req2) |>.step |>.assertHasEndHeaders |>.assertKeepAlive
    |>.send { status := .ok } |>.setKnownSize (.fixed 0) |>.userClosedBody
    |>.drainBody |>.step |>.assertHasNext
    |>.step |>.assertHasEndHeaders |>.run

  -- §19.7.1: client side — response Connection:keep-alive → keepAlive = true
  MachineTester.sending "§19.7.1: client receives HTTP/1.0 + Connection:keep-alive → keepAlive = true"
    |>.send minimalGetRequest |>.step
    |>.feed "HTTP/1.0 200 OK\r\nConnection: keep-alive\r\nContent-Length: 0\r\n\r\n"
    |>.step |>.assertNoError |>.assertKeepAlive |>.run

  -- §19.7.1: when serving an HTTP/1.0 keep-alive connection, the response must include
  --          Connection: keep-alive so the client knows to reuse the connection
  MachineTester.receiving "§19.7.1: HTTP/1.0 keep-alive → Connection: keep-alive injected in response"
    |>.feed "GET / HTTP/1.0\r\nConnection: keep-alive\r\n\r\n"
    |>.step |>.assertKeepAlive
    |>.send { status := .ok } |>.setKnownSize (.fixed 0) |>.userClosedBody
    |>.step |>.step
    |>.assertOutputContains "Connection: keep-alive"
        "RFC 2616 §19.7.1: HTTP/1.0 keep-alive response must include Connection: keep-alive" |>.run
