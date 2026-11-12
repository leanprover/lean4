import Std.Http
import Std.Http.Test.Helpers

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
Drain all immediately-available body chunks: pulls until the body is complete, or until `pullBody`
returns nothing because the machine waits for more data.
-/
def drainBody (t : MachineTester dir) (fuel : Nat := 4096) : MachineTester dir := Id.run do
  let mut t := t
  let mut remaining := fuel
  while remaining > 0 && t.machine.canPullBody do
    remaining := remaining - 1
    let before := t.pulled.size
    t := t.pullBody
    if t.pulled.size == before then break
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

/-- Assert that the machine has not failed. -/
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

/-- Assert that `isWaitingMessage` is true (writer in `waitingHeaders`). -/
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

  for version in ["HTTP/0.9", "HTTP/3.0"] do
    MachineTester.receiving s!"§2: {version} → unsupportedVersion"
      |>.feed s!"GET / {version}\r\nHost: example.com\r\n\r\n"
      |>.step |>.assertFailedWith .unsupportedVersion |>.run

  -- RFC 9110 §6.2: a higher minor version is processed as the highest minor version the recipient
  -- implements
  for version in ["HTTP/1.2", "HTTP/1.9"] do
    MachineTester.receiving s!"§2: {version} request is read as HTTP/1.1"
      |>.feed s!"GET / {version}\r\nHost: example.com\r\n\r\n"
      |>.step |>.assertNoError |>.assertHasEndHeaders |>.assertKeepAlive
      |>.onEndHeaders (fun t head =>
        if head.version != .v11 then t.addError s!"expected HTTP/1.1, got {repr head.version}" else t)
      |>.send { status := .ok } |>.setKnownSize (.fixed 0) |>.userClosedBody |>.step
      |>.assertOutputStartsWith "HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n" "expected an HTTP/1.1 response"
      |>.assertKeepAlive |>.run

  -- RFC 9110 §9.1, RFC 9112 §3: a well-formed method the server does not recognize, or one longer
  -- than any it implements, is answered with 501. Methods are case-sensitive.
  let longMethod := String.ofList (List.replicate 65 'G')
  for (label, method) in [("LEAN", "LEAN"), ("GETX", "GETX"), ("get", "get"), ("X-CUSTOM", "X-CUSTOM"),
      ("UPDATEX", "UPDATEX"), ("a 65-byte token", longMethod)] do
    MachineTester.receiving s!"§3: unrecognized method {label} → unsupportedMethod"
      |>.feed s!"{method} / HTTP/1.1\r\nHost: example.com\r\n\r\n"
      |>.step |>.assertFailedWith .unsupportedMethod
      |>.step |>.assertOutputStartsWith "HTTP/1.1 501 Not Implemented\r\n" "expected 501" |>.run

  -- A method that is not a token makes the request line malformed
  for line in ["G@T / HTTP/1.1", "GÉT / HTTP/1.1", "GET\t/ HTTP/1.1", "GETHTTP/1.1"] do
    MachineTester.receiving s!"§3: {line.quote} → badMessage"
      |>.feed s!"{line}\r\nHost: example.com\r\n\r\n"
      |>.step |>.assertFailedWith .badMessage |>.run

  -- The method is read whole before it is matched, so the outcome does not depend on where a read
  -- ends inside it (#16111: `UPDATE` must not match the start of `UPDATEREDIRECTREF`)
  for expected in Method.all do
    let name := toString expected
    unless Method.ofString? name == some expected do
      throw <| IO.userError s!"Method.ofString? {name.quote} is not {repr expected}"
    let (target, host) := if name == "CONNECT" then ("example.com:443", "example.com:443") else ("/", "example.com")
    let request := s!"{name} {target} HTTP/1.1\r\nHost: {host}\r\n\r\n".toUTF8
    for i in [1:name.length + 2] do
      MachineTester.receiving s!"§3: {name} split after byte {i}"
        |>.feedBytes (request.extract 0 i) |>.step |>.assertNoError
        |>.feedBytes (request.extract i request.size) |>.step |>.assertNoError
        |>.onEndHeaders (fun t head =>
          if head.method == expected then t else t.addError s!"expected {name}, got {repr head.method}")
        |>.run

  for method in ["LEAN", "GETX", "UPDATEX", "UPDATEREDIRECTREFS"] do
    let request := s!"{method} / HTTP/1.1\r\nHost: example.com\r\n\r\n".toUTF8
    for i in [1:method.length + 1] do
      MachineTester.receiving s!"§3: unrecognized {method} split after byte {i} → unsupportedMethod"
        |>.feedBytes (request.extract 0 i) |>.step |>.assertNoError
        |>.feedBytes (request.extract i request.size) |>.step
        |>.assertFailedWith .unsupportedMethod |>.run

  MachineTester.receiving "§3: GET method and HTTP/1.1 version parsed correctly"
    |>.feed "GET /path HTTP/1.1\r\nHost: example.com\r\n\r\n"
    |>.step |>.assertNoError
    |>.onEndHeaders (fun t head =>
      if head.method != .get then t.addError s!"expected method GET, got {repr head.method}"
      else if head.version != .v11 then t.addError s!"expected HTTP/1.1, got {repr head.version}"
      else t)
    |>.run

#eval runGroup "RFC 9110 §2.5, §5.5 / RFC 9112 §4: response start line and field values" do
  -- §5.5: a recipient treats obs-text in a field value as opaque data
  MachineTester.sending "§5.5: obs-text in a response field value is accepted"
    |>.send minimalGetRequest |>.step
    |>.feedBytes ("HTTP/1.1 200 OK\r\nContent-Disposition: attachment; filename=\"caf".toUTF8
      ++ ByteArray.mk #[0xC3, 0xA9] ++ ".txt\"\r\nX-Latin1: caf".toUTF8 ++ ByteArray.mk #[0xE9]
      ++ "\r\nContent-Length: 0\r\n\r\n".toUTF8)
    |>.step |>.assertNoError |>.assertHasEndHeaders
    |>.onEndHeaders (fun t head =>
      let disposition := (head.headers.get? (.ofString! "Content-Disposition")).map (·.value)
      let latin1 := (head.headers.get? (.ofString! "X-Latin1")).map (·.value)
      if disposition != some "attachment; filename=\"café.txt\"" then
        t.addError s!"Content-Disposition mismatch: {repr disposition}"
      else if latin1 != some "caf\uFFFD" then
        t.addError s!"X-Latin1 mismatch: {repr latin1}"
      else t)
    |>.run

  -- §4: obs-text in a reason phrase, which a client ignores
  MachineTester.sending "§4: obs-text in the reason phrase is accepted"
    |>.send minimalGetRequest |>.step
    |>.feedBytes ("HTTP/1.1 200 Tr".toUTF8 ++ ByteArray.mk #[0xC3, 0xA8] ++ "s bien ".toUTF8
      ++ ByteArray.mk #[0xFF] ++ "\r\nContent-Length: 0\r\n\r\n".toUTF8)
    |>.step |>.assertNoError
    |>.onEndHeaders (fun t head =>
      if head.status.toCode != 200 then t.addError s!"expected 200, got {head.status.toCode}" else t)
    |>.run

  -- §4: a status line that ends right after the status code
  MachineTester.sending "§4: status line with no space after the code is accepted"
    |>.send minimalGetRequest |>.step
    |>.feed "HTTP/1.1 204\r\n\r\n"
    |>.step |>.assertNoError
    |>.onEndHeaders (fun t head =>
      if head.status != .noContent then t.addError s!"expected 204, got {head.status.toCode}" else t)
    |>.run

  -- §2.5: a higher minor version is processed as the highest minor version the recipient implements
  MachineTester.sending "§2.5: HTTP/1.2 response is read as HTTP/1.1"
    |>.send minimalGetRequest |>.step
    |>.feed "HTTP/1.2 200 OK\r\nContent-Length: 2\r\n\r\nok"
    |>.step |>.assertNoError |>.assertKeepAlive
    |>.onEndHeaders (fun t head =>
      if head.version != .v11 then t.addError s!"expected HTTP/1.1, got {repr head.version}" else t)
    |>.drainBody |>.assertPulledBody "ok".toUTF8 |>.run

#eval runGroup "RFC 9112 §7.1.2 / RFC 9110 §6.5: trailer fields" do
  -- §6.5.1: a client drops a trailer field it must not process instead of failing the response
  MachineTester.sending "§6.5: forbidden non-framing trailer field in a response is dropped"
    |>.send minimalGetRequest |>.step
    |>.feed "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n2\r\nok\r\n0\r\nCache-Control: no-cache\r\n\r\n"
    |>.step |>.assertNoError
    |>.drainBody |>.assertNoError |>.assertPulledBody "ok".toUTF8 |>.assertLastChunkFinal |>.run

  -- a field that frames the message is still refused in a response's trailers
  MachineTester.sending "§6.5: framing field in response trailers → badMessage"
    |>.send minimalGetRequest |>.step
    |>.feed "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n2\r\nok\r\n0\r\nContent-Length: 2\r\n\r\n"
    |>.step |>.drainBody |>.assertFailedWith .badMessage |>.run

  -- a server keeps rejecting every field forbidden in a request's trailers
  MachineTester.receiving "§6.5: forbidden trailer field in a request → badMessage"
    |>.feed (mkChunkedPost "/" ++ "2\r\nok\r\n0\r\nCache-Control: no-cache\r\n\r\n")
    |>.step |>.drainBody |>.assertFailedWith .badMessage |>.run

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

  -- RFC 9110 §7.2: `Host` is an RFC 3986 `host`, which may be percent-encoded. The field reaches the
  -- handler as sent.
  MachineTester.receiving "§3.2: percent-encoded Host accepted"
    |>.feed "GET / HTTP/1.1\r\nHost: ex%41mple.com\r\n\r\n"
    |>.step |>.assertNoError
    |>.onEndHeaders (fun t head =>
      match head.headers.get? .host with
      | some v => if v.value == "ex%41mple.com" then t else t.addError s!"expected Host=ex%41mple.com, got {v.value.quote}"
      | none => t.addError "missing Host header")
    |>.run

  MachineTester.receiving "§3.3: percent-encoded absolute-form host decoded"
    |>.feed "GET http://ex%41mple.com/ HTTP/1.1\r\nHost: example.com\r\n\r\n"
    |>.step |>.assertNoError
    |>.onEndHeaders (fun t head =>
      match head.uri.authority? with
      | some a => if toString a == "example.com" then t else t.addError s!"expected URI authority=example.com, got {toString a}"
      | none => t.addError "missing URI authority")
    |>.run

  MachineTester.receiving "§3.2: Host with a percent-encoded `/` → badMessage"
    |>.feed "GET / HTTP/1.1\r\nHost: exa%2Fmple.com\r\n\r\n"
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

#eval runGroup "RFC 9112 §6: Transfer-Encoding validation" do
  -- RFC 9110 §5.3: the field lines of Transfer-Encoding form one list, so these are `gzip, chunked`
  MachineTester.receiving "§6.1: gzip and chunked on two field lines → unsupportedTransferCoding"
    |>.feed "POST / HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: gzip\r\nTransfer-Encoding: chunked\r\n\r\n"
    |>.step |>.assertFailedWith .unsupportedTransferCoding |>.run

  MachineTester.receiving "§6.1: chunked on two field lines is chunked applied twice → badMessage"
    |>.feed "POST / HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: chunked\r\nTransfer-Encoding: chunked\r\n\r\n"
    |>.step |>.assertFailedWith .badMessage |>.run

  MachineTester.receiving "§6.3: Transfer-Encoding on two field lines with Content-Length → badMessage"
    |>.feed ("POST / HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: gzip\r\n" ++
      "Transfer-Encoding: chunked\r\nContent-Length: 3\r\n\r\n")
    |>.step |>.assertFailedWith .badMessage |>.run

  -- RFC 9110 §5.6.1.2: empty list elements are ignored
  MachineTester.receiving "§6.1: accepted codings over two field lines with empty elements"
      (config := { acceptedTransferCodings := #["gzip"] })
    |>.feed ("POST / HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: gzip, \r\n" ++
      "Transfer-Encoding: , chunked\r\n\r\n3\r\nabc\r\n0\r\n\r\n")
    |>.step |>.assertNoError
    |>.drainBody |>.assertNoError |>.assertPulledBody "abc".toUTF8 |>.assertLastChunkFinal |>.run

  MachineTester.receiving "§6.1: Transfer-Encoding: gzip, , chunked → unsupportedTransferCoding"
    |>.feed "POST / HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: gzip, , chunked\r\n\r\n"
    |>.step |>.assertFailedWith .unsupportedTransferCoding |>.run

  MachineTester.receiving "§6.1: Transfer-Encoding: identity → badMessage"
    |>.feed "POST / HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: identity\r\n\r\n"
    |>.step |>.assertFailedWith .badMessage |>.run

  -- §6.1: a server answers a transfer coding it does not understand with 501; only `chunked` is
  -- decoded, so any other coding before it is not implemented
  for coding in ["gzip, chunked", "br, chunked", "gzip;level=1, chunked", "x-custom, gzip, chunked"] do
    MachineTester.receiving s!"§6.1: Transfer-Encoding: {coding} request → 501 Not Implemented"
      |>.feed (s!"POST / HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: {coding}\r\n\r\n" ++
        "3\r\nabc\r\n0\r\n\r\n")
      |>.step |>.assertFailedWith .unsupportedTransferCoding
      |>.step
      |>.assertOutputStartsWith "HTTP/1.1 501 Not Implemented\r\n" "expected 501"
      |>.assertOutputContains "Connection: close\r\n" "the unread body ends the connection" |>.run

  -- §6.3 rule 4: a request whose final coding is not `chunked` has no reliable length: 400, not 501
  MachineTester.receiving "§6.3: Transfer-Encoding: gzip request → badMessage"
    |>.feed "POST / HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: gzip\r\n\r\nabc"
    |>.step |>.assertFailedWith .badMessage |>.run

  -- §6.1: a coding the application decodes itself is accepted; the machine removes only the chunked
  -- framing and keeps the field that says which codings are left
  let teField (expected : String) (t : MachineTester .receiving) (head : Request.Head) :
      MachineTester .receiving :=
    match head.headers.getAll? Header.Name.transferEncoding with
    | some #[value] =>
      if value.value == expected then t
      else t.addError s!"expected Transfer-Encoding {expected.quote}, got {value.value.quote}"
    | _ => t.addError "expected one Transfer-Encoding field"

  MachineTester.receiving "§6.1: accepted gzip;level=1, chunked → body still coded, field kept"
      (config := { acceptedTransferCodings := #["gzip"] })
    |>.feed ("POST / HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: gzip;level=1, chunked\r\n\r\n" ++
      "3\r\nabc\r\n0\r\n\r\n")
    |>.step |>.assertNoError |>.onEndHeaders (teField "gzip;level=1, chunked")
    |>.drainBody |>.assertNoError |>.assertPulledBody "abc".toUTF8 |>.assertLastChunkFinal |>.run

  MachineTester.receiving "§6.1: accepted coding names are compared case-insensitively"
      (config := { acceptedTransferCodings := #["GZIP"] })
    |>.feed ("POST / HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: Gzip, Chunked\r\n\r\n" ++
      "3\r\nabc\r\n0\r\n\r\n")
    |>.step |>.assertNoError |>.onEndHeaders (teField "Gzip, Chunked")
    |>.drainBody |>.assertNoError |>.assertPulledBody "abc".toUTF8 |>.run

  MachineTester.receiving "§6.1: every coding before chunked must be accepted"
      (config := { acceptedTransferCodings := #["gzip"] })
    |>.feed ("POST / HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: br, gzip, chunked\r\n\r\n" ++
      "3\r\nabc\r\n0\r\n\r\n")
    |>.step |>.assertFailedWith .unsupportedTransferCoding |>.run

  -- §6.3 rule 4: an accepted coding does not give a request without a final chunked a length
  MachineTester.receiving "§6.3: accepted gzip without chunked → badMessage"
      (config := { acceptedTransferCodings := #["gzip"] })
    |>.feed "POST / HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: gzip\r\n\r\nabc"
    |>.step |>.assertFailedWith .badMessage |>.run

  -- RFC 9112 §7.1: `chunked` defines no parameters
  MachineTester.receiving "§7: Transfer-Encoding: chunked;x=1 request → badMessage"
    |>.feed "POST / HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: chunked;x=1\r\n\r\n0\r\n\r\n"
    |>.step |>.assertFailedWith .badMessage |>.run

#eval runGroup "RFC 9112 §6.3: body framing" do
  MachineTester.receiving "§6.3: no CL/TE → empty body"
    |>.feed (mkGet "/")
    |>.step |>.assertNoError |>.assertHasEndHeaders
    |>.assertCanPullBody |>.drainBody
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

#eval runGroup "RFC 9112 §6: framing of messages without a body, and of written messages" do
  -- §6.3 rule 1: a response to HEAD ends at its header block, whatever its framing fields say
  MachineTester.sending "§6.3: HEAD response with contradictory framing fields completes"
    |>.send { minimalGetRequest with method := .head } |>.step
    |>.feed "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\nContent-Length: 10\r\n\r\n"
    |>.step |>.assertNoError |>.assertReaderComplete |>.run

  -- §6.3 rule 1: so does a 204 response
  MachineTester.sending "§6.3: 204 response with contradictory framing fields completes"
    |>.send minimalGetRequest |>.step
    |>.feed "HTTP/1.1 204 No Content\r\nTransfer-Encoding: chunked\r\nContent-Length: 5\r\n\r\n"
    |>.step |>.assertNoError |>.assertReaderComplete |>.run

  -- §6.3 rule 4: a response whose final transfer coding is not chunked is read until the server closes
  for coding in ["gzip", "chunked, gzip", "gzip;level=1", "gzip ; level = \"9\""] do
    MachineTester.sending s!"§6.3: Transfer-Encoding: {coding} response is close-delimited"
      |>.send minimalGetRequest |>.step
      |>.feed s!"HTTP/1.1 200 OK\r\nTransfer-Encoding: {coding}\r\n\r\nabc"
      |>.step |>.assertNoError |>.assertNotKeepAlive
      |>.noMoreInput |>.drainBody |>.assertNoError
      |>.assertPulledBody "abc".toUTF8 |>.assertLastChunkFinal |>.run

  -- §7: transfer parameters do not change which coding is final
  MachineTester.sending "§6.3: Transfer-Encoding: gzip;level=1, chunked response is chunked"
    |>.send minimalGetRequest |>.step
    |>.feed "HTTP/1.1 200 OK\r\nTransfer-Encoding: gzip;level=1, chunked\r\n\r\n3\r\nabc\r\n0\r\n\r\n"
    |>.step |>.assertNoError |>.assertKeepAlive
    |>.drainBody |>.assertNoError |>.assertPulledBody "abc".toUTF8 |>.assertLastChunkFinal |>.run

  -- §7.1: chunked defines no parameters
  for coding in ["chunked;x=1", "gzip;level, chunked", "gzip;=1, chunked"] do
    MachineTester.sending s!"§7: Transfer-Encoding: {coding} → badMessage"
      |>.send minimalGetRequest |>.step
      |>.feed s!"HTTP/1.1 200 OK\r\nTransfer-Encoding: {coding}\r\n\r\n3\r\nabc\r\n0\r\n\r\n"
      |>.step |>.assertFailedWith .badMessage |>.run

  -- §6.1: a chunked message keeps the transfer codings its body was coded with
  MachineTester.receiving "§6.1: server keeps the handler's Transfer-Encoding: gzip, chunked"
    |>.feed (mkGet "/") |>.step |>.assertIsWaitingMessage
    |>.send { status := .ok, headers := Headers.empty.insert! "Transfer-Encoding" "gzip, chunked" }
    |>.sendBytes "abc".toUTF8 |>.userClosedBody |>.step
    |>.assertOutputContains "Transfer-Encoding: gzip, chunked\r\n" "expected the handler's codings"
    |>.assertOutputContains "3\r\nabc\r\n0\r\n\r\n" "expected a chunked body" |>.run

  MachineTester.receiving "§6.1: server keeps the handler's Transfer-Encoding: gzip;level=1, chunked"
    |>.feed (mkGet "/") |>.step |>.assertIsWaitingMessage
    |>.send { status := .ok, headers := Headers.empty.insert! "Transfer-Encoding" "gzip;level=1, chunked" }
    |>.sendBytes "abc".toUTF8 |>.userClosedBody |>.step
    |>.assertOutputContains "Transfer-Encoding: gzip;level=1, chunked\r\n" "expected the handler's codings"
    |>.assertOutputContains "3\r\nabc\r\n0\r\n\r\n" "expected a chunked body" |>.run

  MachineTester.sending "§6.1: client keeps the caller's Transfer-Encoding: gzip, chunked"
    |>.send { minimalGetRequest with
      method := .post, headers := minimalGetRequest.headers.insert! "Transfer-Encoding" "gzip, chunked" }
    |>.sendBytes "abc".toUTF8 |>.userClosedBody |>.step
    |>.assertOutputContains "Transfer-Encoding: gzip, chunked\r\n" "expected the caller's codings"
    |>.assertOutputContains "3\r\nabc\r\n0\r\n\r\n" "expected a chunked body" |>.run

  -- RFC 9110 §5.3: codings over several field lines are one list, written as one field
  MachineTester.receiving "§6.1: server writes the handler's two Transfer-Encoding lines as one"
    |>.feed (mkGet "/") |>.step |>.assertIsWaitingMessage
    |>.send { status := .ok, headers :=
      (Headers.empty.insert! "Transfer-Encoding" "gzip").insert! "Transfer-Encoding" "chunked" }
    |>.sendBytes "abc".toUTF8 |>.userClosedBody |>.step
    |>.assertOutputContains "Transfer-Encoding: gzip, chunked\r\n" "expected the combined codings"
    |>.assertOutputNotContains "Transfer-Encoding: chunked\r\n" "expected one Transfer-Encoding field"
    |>.assertOutputContains "3\r\nabc\r\n0\r\n\r\n" "expected a chunked body" |>.run

  -- RFC 9110 §15.3.6: a server must not generate content in a 205 response; it sends
  -- `Content-Length: 0` whatever length or framing the handler gave
  MachineTester.receiving "§15.3.6: 205 drops the handler's content and sends Content-Length: 0"
    |>.feed (mkGet "/") |>.step |>.assertIsWaitingMessage
    |>.send { status := .resetContent } |>.sendBytes "body".toUTF8 |>.userClosedBody |>.step
    |>.assertOutputStartsWith "HTTP/1.1 205 Reset Content\r\nContent-Length: 0\r\n\r\n"
        "expected a 205 head with Content-Length: 0"
    |>.assertOutputNotContains "body" "a 205 response carries no content"
    |>.assertNoError |>.assertKeepAlive |>.run

  MachineTester.receiving "§15.3.6: 205 with the handler's Content-Length: 4 still sends Content-Length: 0"
    |>.feed (mkGet "/") |>.step |>.assertIsWaitingMessage
    |>.send { status := .resetContent, headers := Headers.empty.insert! "Content-Length" "4" }
    |>.sendBytes "body".toUTF8 |>.userClosedBody |>.step
    |>.assertOutputContains "Content-Length: 0\r\n\r\n" "expected Content-Length: 0"
    |>.assertOutputNotContains "Content-Length: 4" "the handler's length must not be advertised"
    |>.assertOutputNotContains "body" "a 205 response carries no content"
    |>.assertNoError |>.run

  MachineTester.receiving "§15.3.6: 205 of unknown length is not chunked"
    |>.feed (mkGet "/") |>.step |>.assertIsWaitingMessage
    |>.send { status := .resetContent } |>.setKnownSize .chunked |>.sendBytes "body".toUTF8
    |>.userClosedBody |>.step
    |>.assertOutputContains "Content-Length: 0\r\n\r\n" "expected Content-Length: 0"
    |>.assertOutputNotContains "Transfer-Encoding" "a 205 response is not chunked"
    |>.assertOutputNotContains "body" "a 205 response carries no content" |>.run

  -- RFC 9110 §8.6: no Content-Length on a request without content whose method anticipates none
  MachineTester.sending "§8.6: bodyless GET request carries no Content-Length"
    |>.send minimalGetRequest |>.userClosedBody |>.step
    |>.assertOutputStartsWith "GET / HTTP/1.1\r\n" "expected the request line"
    |>.assertOutputNotContains "Content-Length" "a bodyless GET must not carry Content-Length" |>.run

  MachineTester.sending "§8.6: bodyless POST request still carries Content-Length: 0"
    |>.send { minimalGetRequest with method := .post } |>.userClosedBody |>.step
    |>.assertOutputContains "Content-Length: 0\r\n" "a bodyless POST keeps Content-Length: 0" |>.run

  MachineTester.sending "§8.6: a GET whose caller set Content-Length: 0 keeps it"
    |>.send { minimalGetRequest with headers := minimalGetRequest.headers.insert! "Content-Length" "0" }
    |>.userClosedBody |>.step
    |>.assertOutputContains "Content-Length: 0\r\n" "an explicit framing field is kept" |>.run

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
    -- The step that ends the exchange goes on to the buffered request.
    |>.assertHasEndHeaders |>.run

  -- §9.3: pipelining after CL:0 body — second request parses correctly
  let post1 := "POST /a HTTP/1.1\r\nHost: example.com\r\nContent-Length: 0\r\n\r\n"
  let get2  := "GET /b HTTP/1.1\r\nHost: example.com\r\n\r\n"
  MachineTester.receiving "§9.3: pipelining after CL:0 body — second request path correct"
    |>.feed (post1 ++ get2) |>.step |>.assertHasEndHeaders
    |>.drainBody |>.assertPulledBody .empty
    |>.send { status := .ok } |>.setKnownSize (.fixed 0) |>.userClosedBody
    |>.step |>.assertHasNext |>.assertHasEndHeaders
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
    |>.drainBody |>.step |>.assertHasNext |>.assertHasEndHeaders
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

  -- §9.6: a `Connection: close` response header set by the handler ends a keep-alive connection
  MachineTester.receiving "§9.6: handler Connection:close on keep-alive request → connection closed"
    |>.feed (mkGet "/first" ++ mkGet "/second") |>.step |>.assertHasEndHeaders |>.assertKeepAlive
    |>.send { status := .ok, headers := Headers.empty.insert .connection (.mk "close") }
    |>.setKnownSize (.fixed 0) |>.userClosedBody |>.step
    |>.assertNotKeepAlive
    |>.assertOutputContains "Connection: close" "expected Connection: close in response"
    |>.assertHasEvent (fun | .close => true | _ => false) "expected .close after the response"
    |>.assertNoEvent (fun | .next => true | _ => false) "expected the pipelined request to be dropped"
    |>.step |>.assertHalted |>.run

  -- §9.6: the error responses of `closeWithError` end a keep-alive connection
  for status in #[Status.internalServerError, .requestTimeout, .serviceUnavailable] do
    MachineTester.receiving s!"§9.6: closeWithError {status.toCode} on keep-alive request → connection closed"
      |>.feed (mkGet "/first" ++ mkGet "/second") |>.step |>.assertHasEndHeaders |>.assertKeepAlive
      |>.closeWithError status |>.step
      |>.assertNotKeepAlive
      |>.assertOutputStartsWith s!"HTTP/1.1 {status.toCode} " "expected the error status line"
      |>.assertOutputContains "Connection: close" "expected Connection: close in the error response"
      |>.assertHasEvent (fun | .close => true | _ => false) "expected .close after the error response"
      |>.assertNoEvent (fun | .next => true | _ => false) "expected the pipelined request to be dropped"
      |>.run

  -- §9.6: HTTP/1.1 response with Connection: close → keep-alive disabled
  MachineTester.sending "§9.6: HTTP/1.1 response Connection:close → keep-alive = false"
    |>.send minimalGetRequest |>.step
    |>.feed "HTTP/1.1 200 OK\r\nConnection: close\r\nContent-Length: 0\r\n\r\n"
    |>.step |>.assertNoError |>.assertNotKeepAlive |>.run

  -- RFC 9110 §7.6.1, §7.8: the handler's connection options are kept, with the machine's `close`
  let upgrade (connection : String) : Response.Head :=
    { status := .upgradeRequired,
      headers := Headers.empty |>.insert! "Upgrade" "TLS/1.2" |>.insert! "Connection" connection }
  MachineTester.receiving "§7.8: 426 keeps Connection: upgrade and appends close"
    |>.feed "GET / HTTP/1.1\r\nHost: example.com\r\nConnection: close\r\n\r\n"
    |>.step |>.assertIsWaitingMessage
    |>.send (upgrade "Upgrade")
    |>.setKnownSize (.fixed 0) |>.userClosedBody |>.step
    |>.assertOutputContains "Connection: upgrade, close\r\n" "expected the handler's upgrade option and close"
    |>.assertOutputContains "Upgrade: TLS/1.2\r\n" "expected the Upgrade field" |>.run

  MachineTester.receiving "§7.8: keep-alive response keeps the handler's Connection: upgrade"
    |>.feed (mkGet "/") |>.step |>.assertKeepAlive
    |>.send (upgrade "upgrade, keep-alive")
    |>.setKnownSize (.fixed 0) |>.userClosedBody |>.step |>.assertKeepAlive
    |>.assertOutputContains "Connection: upgrade\r\n" "expected only the upgrade option" |>.run

  -- RFC 9110 §7.8: a client that sends `Upgrade` also sends the `upgrade` connection option
  MachineTester.sending "§7.8: client keeps the caller's Connection: upgrade"
    |>.send { minimalGetRequest with
      headers := minimalGetRequest.headers
        |>.insert! "Connection" "Upgrade" |>.insert! "Upgrade" "websocket" }
    |>.userClosedBody |>.step
    |>.assertOutputContains "Connection: upgrade\r\n" "expected the caller's upgrade option"
    |>.assertOutputContains "Upgrade: websocket\r\n" "expected the Upgrade field" |>.run

  MachineTester.sending "§7.8: client appends close to the caller's connection options"
    |>.send { minimalGetRequest with
      headers := minimalGetRequest.headers
        |>.insert! "Connection" "upgrade, close" |>.insert! "Upgrade" "websocket" }
    |>.userClosedBody |>.step |>.assertNotKeepAlive
    |>.assertOutputContains "Connection: upgrade, close\r\n" "expected the upgrade option, then close"
    |>.run

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
    |>.feedBytes body |>.step |>.assertCanPullBody
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

  -- §15.2: an interim response has no body of its own, so it must not end the response body
  MachineTester.sending "§15.2: 103 Early Hints → no closeBody until the final response"
    |>.send minimalGetRequest |>.step
    |>.feed "HTTP/1.1 103 Early Hints\r\nLink: </style.css>; rel=preload\r\n\r\n" |>.step
    |>.assertNoError
    |>.assertNoEvent (fun | .closeBody => true | _ => false)
        "an interim response must not emit closeBody"
    |>.feed "HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nok" |>.step
    |>.drainBody |>.assertNoError |>.assertPulledBody "ok".toUTF8
    |>.assertHasCloseBody |>.run

  -- §15.2.2: after 101 the connection speaks the new protocol, so no final response follows and the
  -- bytes after the head are not read as HTTP
  MachineTester.sending "§15.2.2: 101 Switching Protocols ends the exchange"
    |>.send { minimalGetRequest with
      headers := minimalGetRequest.headers
        |>.insert! "Connection" "upgrade" |>.insert! "Upgrade" "websocket" }
    |>.step
    |>.feed "HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n\r\n"
    |>.feedBytes (ByteArray.mk #[0x81, 0x02, 0x68, 0x69])
    |>.step
    |>.assertNoError |>.assertHasEndHeaders |>.assertNotKeepAlive
    |>.assertReaderClosed |>.run

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

  -- RFC 9110 §9.3.2, §8.6: with no known length a HEAD response has GET's framing; a
  -- `Content-Length: 0` would claim the GET response is empty
  MachineTester.receiving "§9.3.2: HEAD response of unknown length has no Content-Length: 0"
    |>.feed ("HEAD / HTTP/1.1\r\nHost: example.com\r\n\r\n" ++ mkGet "/next")
    |>.step |>.assertIsWaitingMessage
    |>.send { status := .ok } |>.userClosedBody |>.step
    |>.assertOutputNotContains "Content-Length" "unknown length must not be sent as Content-Length: 0"
    |>.assertOutputContains "Transfer-Encoding: chunked\r\n" "expected the framing GET would have"
    |>.assertOutputNotContains "0\r\n\r\n" "a HEAD response carries no body, not even a last chunk"
    |>.assertHasNext |>.run

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
    |>.drainBody |>.step |>.assertHasNext |>.assertHasEndHeaders |>.run

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

  -- RFC 9110 §15.2: a server must not send a 1xx response to an HTTP/1.0 client
  MachineTester.receiving "§15.2: 103 Early Hints is not sent to an HTTP/1.0 client"
    |>.feed (mkGet10 "/") |>.step |>.assertIsWaitingMessage
    |>.send { status := .earlyHints, headers := Headers.empty.insert! "Link" "</a.css>; rel=preload" }
    |>.step |>.assertIsWaitingMessage
    |>.send { status := .ok } |>.setKnownSize (.fixed 0) |>.userClosedBody |>.step
    |>.assertOutputNotContains "103" "a 1xx response must not reach an HTTP/1.0 client"
    |>.assertOutputStartsWith "HTTP/1.1 200" "expected the final response first" |>.run

  -- RFC 9110 §6.2: a server sends the highest version it conforms to whose major version is at most
  -- the request's, so an HTTP/1.0 request gets an HTTP/1.1 status line with HTTP/1.0 framing
  MachineTester.receiving "§6.2: HTTP/1.0 request → HTTP/1.1 status line, connection-close framing"
    |>.feed (mkGet10 "/") |>.step
    |>.send { status := .ok } |>.sendBytes "hello".toUTF8 |>.userClosedBody
    |>.step |>.step
    |>.assertOutputStartsWith "HTTP/1.1 200 OK\r\n" "expected an HTTP/1.1 status line"
    |>.assertOutputContains "Connection: close\r\n" "an HTTP/1.0 connection without keep-alive closes"
    |>.assertOutputNotContains "Transfer-Encoding" "HTTP/1.0 has no chunked framing" |>.run

  MachineTester.receiving "§6.2: HTTP/1.0 keep-alive request → HTTP/1.1 status line, keep-alive echoed"
    |>.feed "GET / HTTP/1.0\r\nConnection: keep-alive\r\n\r\n" |>.step
    |>.send { status := .ok } |>.setKnownSize (.fixed 0) |>.userClosedBody
    |>.step |>.step
    |>.assertOutputStartsWith "HTTP/1.1 200 OK\r\n" "expected an HTTP/1.1 status line"
    |>.assertOutputContains "Connection: keep-alive\r\n" "expected the HTTP/1.0 keep-alive echo"
    |>.assertKeepAlive |>.run

  -- RFC 9112 §6.3: a HEAD response ends at its header block, so a length the server does not know
  -- does not cost an HTTP/1.0 client its keep-alive connection
  MachineTester.receiving "§6.3: HTTP/1.0 HEAD of unknown length keeps the connection alive"
    |>.feed ("HEAD / HTTP/1.0\r\nConnection: keep-alive\r\n\r\n" ++
      "GET /second HTTP/1.0\r\nConnection: keep-alive\r\n\r\n")
    |>.step |>.assertIsWaitingMessage
    |>.send { status := .ok } |>.userClosedBody |>.step
    |>.assertOutputContains "Connection: keep-alive\r\n" "expected the HTTP/1.0 keep-alive echo"
    |>.assertOutputNotContains "Content-Length" "unknown length must not be sent as Content-Length: 0"
    |>.assertOutputNotContains "close" "a HEAD response has no body to delimit by closing"
    |>.assertHasNext |>.assertHasEndHeaders |>.assertKeepAlive |>.run

#eval runGroup "RFC 9110 §6.6.1: Date" do
  let date : Header.Value := .mk "Mon, 01 Jan 2024 00:00:00 GMT"
  let withDate (t : MachineTester .receiving) : MachineTester .receiving :=
    { t with machine := { t.machine with date := some date } }

  MachineTester.receiving "§6.6.1: the machine's date goes into a response without Date"
    |> withDate
    |>.feed (mkGet "/") |>.step
    |>.send { status := .ok } |>.setKnownSize (.fixed 0) |>.userClosedBody |>.step
    |>.assertOutputStartsWith "HTTP/1.1 200 OK\r\nDate: Mon, 01 Jan 2024 00:00:00 GMT\r\nContent-Length: 0\r\n"
        "expected the machine's Date after the handler's fields" |>.run

  MachineTester.receiving "§6.6.1: the handler's own Date is kept and not duplicated"
    |> withDate
    |>.feed (mkGet "/") |>.step
    |>.send { status := .ok, headers := Headers.empty.insert! "Date" "Tue, 02 Jan 2024 00:00:00 GMT" }
    |>.setKnownSize (.fixed 0) |>.userClosedBody |>.step
    |>.assertOutputContains "Date: Tue, 02 Jan 2024 00:00:00 GMT\r\n" "expected the handler's Date"
    |>.assertOutputNotContains "Mon, 01 Jan 2024" "the machine's Date must not be added too" |>.run

  MachineTester.receiving "§6.6.1: a 400 the machine writes itself carries Date"
    |> withDate
    |>.feed "GET / HTTP/1.1\r\n\r\n" |>.step |>.step
    |>.assertOutputStartsWith
        "HTTP/1.1 400 Bad Request\r\nContent-Type: text/plain; charset=utf-8\r\nDate: Mon, 01 Jan 2024 00:00:00 GMT\r\n"
        "expected Date on the machine's 400" |>.run

  MachineTester.receiving "§6.6.1: a 408 from closeWithError carries Date"
    |> withDate
    |>.feed (mkPostHead "/" 5) |>.step
    |>.closeWithError .requestTimeout |>.step
    |>.assertOutputStartsWith
        "HTTP/1.1 408 Request Timeout\r\nContent-Type: text/plain; charset=utf-8\r\nDate: Mon, 01 Jan 2024 00:00:00 GMT\r\n"
        "expected Date on the 408" |>.run

  MachineTester.receiving "§6.6.1: the 500 for a rejected head carries Date and an explanation"
    |> withDate
    |>.feed (mkGet "/") |>.step
    |>.setKnownSize (.fixed 0)
    |>.send { status := .ok, headers := Headers.empty.insert! "Content-Length" "4" } |>.step
    |>.assertOutputStartsWith
        ("HTTP/1.1 500 Internal Server Error\r\nContent-Type: text/plain; charset=utf-8\r\n" ++
          "Date: Mon, 01 Jan 2024 00:00:00 GMT\r\nConnection: close\r\nContent-Length: 22\r\n\r\n" ++
          "Internal Server Error\n")
        "expected Date and the explanation on the 500" |>.run

  MachineTester.receiving "§6.6.1: without a date the machine adds no Date"
    |>.feed "GET / HTTP/1.1\r\n\r\n" |>.step |>.step
    |>.assertOutputNotContains "Date" "no Date without a date value" |>.run

#eval runGroup "RFC 9110 §15.5, §15.6: content of the error responses the server writes" do
  -- §15.5, §15.6: except for a response to HEAD, a 4xx or 5xx response should explain the error
  MachineTester.receiving "§15.5: a 400 the machine writes explains itself"
    |>.feed "GET / HTTP/1.1\r\n\r\n" |>.step |>.step
    |>.assertOutputStartsWith
        ("HTTP/1.1 400 Bad Request\r\nContent-Type: text/plain; charset=utf-8\r\n" ++
          "Connection: close\r\nContent-Length: 12\r\n\r\nBad Request\n")
        "expected a text/plain explanation" |>.run

  -- §15.6.6: a 505 says which versions the server supports
  MachineTester.receiving "§15.6.6: a 505 names the supported versions"
    |>.feed "GET / HTTP/2.0\r\nHost: example.com\r\n\r\n" |>.step |>.step
    |>.assertOutputStartsWith "HTTP/1.1 505 HTTP Version Not Supported\r\n" "expected 505"
    |>.assertOutputContains "\r\n\r\nHTTP Version Not Supported: this server supports HTTP/1.0 and HTTP/1.1\n"
        "expected the supported versions" |>.run

  -- §9.3.2: a response to HEAD has no content, but keeps the Content-Length GET would have
  MachineTester.receiving "§9.3.2: a 400 to HEAD keeps Content-Length and omits the content"
    |>.feed "HEAD / HTTP/1.1\r\n\r\n" |>.step |>.step
    |>.assertOutputStartsWith "HTTP/1.1 400 Bad Request\r\n" "expected 400"
    |>.assertOutputContains "Content-Length: 12\r\n\r\n" "expected the content's length"
    |>.assertOutputNotContains "\r\n\r\nBad Request" "a HEAD response carries no content" |>.run

  MachineTester.receiving "§15.5: a 408 from closeWithError explains itself"
    |>.feed (mkPostHead "/" 5) |>.step
    |>.closeWithError .requestTimeout |>.step
    |>.assertOutputStartsWith "HTTP/1.1 408 Request Timeout\r\n" "expected 408"
    |>.assertOutputContains "Connection: close\r\n" "expected Connection: close"
    |>.assertOutputContains "Content-Length: 16\r\n\r\nRequest Timeout\n" "expected an explanation"
    |>.assertNotKeepAlive |>.run

  MachineTester.receiving "§15.5: a 417 from canContinue explains itself"
    |>.feed (mkPostHead "/" 5 "Expect: 100-continue\r\n") |>.step |>.assertHasContinue
    |>.canContinue .expectationFailed |>.step
    |>.assertOutputStartsWith "HTTP/1.1 417 Expectation Failed\r\n" "expected 417"
    |>.assertOutputContains "Content-Length: 19\r\n\r\nExpectation Failed\n" "expected an explanation"
    |>.assertNotKeepAlive |>.run

  -- A final response sent before the rejection keeps its length and body; the rejection only stops
  -- the request body and the connection
  MachineTester.receiving "§15.5: canContinue after a final response leaves that response intact"
    |>.feed (mkPostHead "/" 5 "Expect: 100-continue\r\n") |>.step |>.assertHasContinue
    |>.setKnownSize (.fixed 5) |>.send { status := .ok } |>.sendBytes "hello".toUTF8 |>.userClosedBody
    |>.canContinue .expectationFailed |>.step |>.step
    |>.assertOutputStartsWith "HTTP/1.1 200 OK\r\nConnection: close\r\nContent-Length: 5\r\n\r\nhello"
        "expected the 200 with its own length and body"
    |>.assertOutputNotContains "Expectation Failed" "no 417 content after a final response"
    |>.assertNoError |>.assertNotKeepAlive |>.run

#eval runGroup "RFC 9110 §8.6 / §6.3: client-side bodyless response framing" do
  -- §8.6: a HEAD response has no body regardless of framing headers. The client reader must treat
  -- it as zero-length and finish without blocking, even though Content-Length advertises bytes that
  -- never arrive on the wire.
  MachineTester.sending "§8.6: client HEAD response — body suppressed despite Content-Length"
    |>.send { minimalGetRequest with method := .head } |>.step
    |>.feed "HTTP/1.1 200 OK\r\nContent-Length: 100\r\n\r\n"
    |>.step
    |>.assertNoError
    |>.assert (fun m => !m.canPullBody)
        "HEAD response must expose no body to pull (reader must not block on absent body bytes)"
    |>.assertReaderComplete |>.run

  -- §6.3: a client response with a known zero-length body (e.g. 204) must auto-complete; otherwise
  -- the connection would stall waiting for a `pullBody` that never produces bytes.
  MachineTester.sending "§6.3: client zero-length response auto-completes without pullBody"
    |>.send minimalGetRequest |>.step
    |>.feed "HTTP/1.1 204 No Content\r\nContent-Length: 0\r\n\r\n"
    |>.step
    |>.assertNoError
    |>.assert (fun m => !m.canPullBody)
        "zero-length response body must not require a caller pullBody to advance"
    |>.assertReaderComplete |>.run

----------------------------------------------------------------------------------------------------

private def connectRequest : Request.Head :=
  { method := .connect, version := .v11, uri := RequestTarget.parse! "example.com:443",
    headers := Headers.empty.insert! "Host" "example.com:443" }

/-- Feeds `raw` one byte per read after sending `minimalGetRequest`, and returns the response head. -/
private def headOneBytePerRead (raw : String) : Option (Message.Head .sending) := Id.run do
  let mut machine := (({ config := {} } : Machine .sending).send minimalGetRequest).step.1
  for b in raw.toUTF8 do
    let (next, result) := (machine.feed (ByteArray.mk #[b])).step
    machine := next
    for e in result.events do
      if let .endHeaders head := e then return some head
  return none

#eval runGroup "RFC 9112 §6.3 rule 2: a 2xx to CONNECT ends at its head" do
  for framing in ["Content-Length: 5\r\n", "Transfer-Encoding: chunked\r\n", ""] do
    MachineTester.sending s!"CONNECT, 200 with {framing.quote}"
      |>.send connectRequest |>.step
      |>.feed s!"HTTP/1.1 200 OK\r\n{framing}\r\n\x16\x03\x01tunnel bytes" |>.step
      |>.assertNoError |>.assertHasEndHeaders |>.drainBody |>.assertPulledBody .empty
      |>.assertReaderClosed |>.assertNotKeepAlive
      |>.assert (·.reader.input.remainingBytes == 15) "expected the tunnel bytes unread" |>.run
  -- A response to CONNECT that is not 2xx is framed as usual.
  MachineTester.sending "CONNECT, 407 with Content-Length: 2"
    |>.send connectRequest |>.step
    |>.feed "HTTP/1.1 407 Proxy Authentication Required\r\nContent-Length: 2\r\n\r\nno" |>.step
    |>.assertNoError |>.drainBody |>.assertPulledBody "no".toUTF8 |>.run

#eval runGroup "RFC 9112 §5.2: a client replaces each obs-fold with SP" do
  for (field, want) in [
      ("X-Fold: text\r\n folded with space\r\n\tfolded with tab", "text folded with space folded with tab"),
      ("X-Fold:\r\n text", "text"), ("X-Fold: text\r\n ", "text"), ("X-Fold:\r\n ", "")] do
    let raw := s!"HTTP/1.1 200 OK\r\n{field}\r\nContent-Length: 0\r\n\r\n"
    MachineTester.sending s!"obs-fold {field.quote}"
      |>.send minimalGetRequest |>.step |>.feed raw |>.step |>.assertNoError
      |>.onEndHeaders (fun t head =>
        let got := (head.headers.get? (.ofString! "X-Fold")).map (·.value)
        if got == some want then t else t.addError s!"expected {want.quote}, got {repr got}")
      |>.run
    let got := (headOneBytePerRead raw).bind fun head => (head.headers.get? (.ofString! "X-Fold")).map (·.value)
    unless got == some want do
      throw <| IO.userError s!"one byte per read, {field.quote}: expected {want.quote}, got {repr got}"
  -- A whitespace line before the first field folds nothing, and a server rejects obs-fold.
  MachineTester.sending "SP line before the first field"
    |>.send minimalGetRequest |>.step |>.feed "HTTP/1.1 200 OK\r\n Foo: bar\r\nContent-Length: 0\r\n\r\n" |>.step
    |>.assertFailedWith .badMessage |>.run
  MachineTester.receiving "obs-fold in a request"
    |>.feed "GET / HTTP/1.1\r\nHost: a\r\nX-Fold: a\r\n b\r\n\r\n" |>.step
    |>.assertFailedWith .badMessage |>.run

#eval runGroup "RFC 9112 §6.3 rule 5: an invalid response Content-Length ends the connection" do
  MachineTester.sending "Content-Length: -1"
    |>.send minimalGetRequest |>.step |>.feed "HTTP/1.1 200 OK\r\nContent-Length: -1\r\n\r\n" |>.step
    |>.assert (·.failed) "expected a failure" |>.assertNotKeepAlive |>.run

#eval runGroup "RFC 9112 §8: EOF before a final response is an incomplete exchange" do
  MachineTester.sending "before any status line"
    |>.send minimalGetRequest |>.step |>.noMoreInput |>.step
    |>.assertFailedWith .connectionClosed |>.run
  MachineTester.sending "after only 100 Continue"
    |>.send minimalGetRequest |>.step |>.feed "HTTP/1.1 100 Continue\r\n\r\n" |>.step |>.noMoreInput |>.step
    |>.assertFailedWith .connectionClosed |>.run
  -- With no request outstanding, EOF is a normal close.
  MachineTester.sending "after a complete response"
    |>.send minimalGetRequest |>.step |>.feed "HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n" |>.step |>.step
    |>.noMoreInput |>.step |>.assertNoError |>.run

-- 600–999 keep their code; 000–099, which `Status` cannot hold, are read as 500.
#eval runGroup "RFC 9110 §15: a client reads status codes outside 100–599 as server errors" do
  for (digits, want) in [("000", 500), ("001", 500), ("099", 500), ("600", 600), ("999", 999)] do
    MachineTester.sending s!"status {digits}"
      |>.send minimalGetRequest |>.step |>.feed s!"HTTP/1.1 {digits} X\r\nContent-Length: 0\r\n\r\n" |>.step
      |>.assertNoError
      |>.onEndHeaders (fun t head =>
        if head.status.isServerError && head.status.toCode.toNat == want then t
        else t.addError s!"got {head.status.toCode}, isServerError {head.status.isServerError}")
      |>.run

#eval runGroup "RFC 9112 §3: a request line with no version fails at once" do
  for raw in ["GET /\r\n\r\n", "GET /x\r\nHost:a\r\n\r\n", "GET /\r"] do
    MachineTester.receiving raw.quote |>.feed raw |>.step |>.assertFailedWith .badMessage |>.run
  -- A target cut off by the end of a read still waits for the rest.
  MachineTester.receiving "GET /" |>.feed "GET /" |>.step |>.assertNoError |>.run

#eval runGroup "RFC 9110 §4.2.4: userinfo in an http(s) request target is an error" do
  for target in ["http://user:pass@example.com/", "https://user@example.com/x"] do
    MachineTester.receiving target
      |>.feed s!"GET {target} HTTP/1.1\r\nHost: example.com\r\n\r\n" |>.step
      |>.assertFailedWith .badMessage |>.run
  MachineTester.receiving "absolute-form without userinfo"
    |>.feed "GET http://example.com/ HTTP/1.1\r\nHost: example.com\r\n\r\n" |>.step
    |>.assertNoError |>.assertHasEndHeaders |>.run

#eval runGroup "Interim responses count toward maxHeaderBytes" do
  -- 54 bytes of each interim head count: its status line and its field line.
  let interim := "HTTP/1.1 100 Continue\r\nX-Pad: 0123456789012345678901\r\n\r\n"
  let mut t := MachineTester.sending "a run of 1xx responses" (config := { maxHeaderBytes := 200 })
    |>.send minimalGetRequest |>.step
  for _ in [0:20] do
    t := t.feed interim |>.step
  t.assertFailedWith .headersTooLarge |>.run
  MachineTester.sending "two 1xx responses, then the final one" (config := { maxHeaderBytes := 200 })
    |>.send minimalGetRequest |>.step |>.feed interim |>.step |>.feed interim |>.step
    |>.feed "HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n" |>.step
    |>.assertNoError |>.assertHasEndHeaders |>.run

#eval runGroup "RFC 9110 §10.1.1: a final response while 100-continue is pending says close" do
  MachineTester.receiving "final response before canContinue"
    |>.feed (mkPostHead "/upload" 5 "Expect: 100-continue\r\n") |>.step |>.assertHasContinue
    |>.send { status := .ok } |>.setKnownSize (.fixed 0) |>.userClosedBody |>.step |>.step
    |>.assertOutputStartsWith "HTTP/1.1 200 OK\r\n" "expected the 200"
    |>.assertOutputContains "Connection: close\r\n" "expected Connection: close"
    |>.assertNotKeepAlive |>.run
  MachineTester.receiving "final response after 100 Continue"
    |>.feed (mkPostHead "/upload" 5 "Expect: 100-continue\r\n") |>.step |>.assertHasContinue
    |>.canContinue .«continue» |>.step |>.feed "hello" |>.step |>.drainBody
    |>.send { status := .ok } |>.setKnownSize (.fixed 0) |>.userClosedBody |>.step |>.step
    |>.assertOutputStartsWith "HTTP/1.1 100 Continue\r\n\r\nHTTP/1.1 200 OK\r\n" "expected 100, then 200"
    |>.assertOutputNotContains "Connection: close" "the connection stays open"
    |>.assertKeepAlive |>.run
