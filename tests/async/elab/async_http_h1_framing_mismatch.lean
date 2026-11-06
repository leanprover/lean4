import Std.Http
import Std.Http.Test.Helpers

open Std.Async
open Std Http Internal Test
open Std.Http.Protocol.H1

/-!
Tests a message head whose framing fields contradict the body length set for it, such as a handler
response with `Content-Length: 3` and a streamed body. The server answers `500 Internal Server
Error` and closes the connection instead of spinning in its connection loop, and a client ends the
exchange. A response that carries no body (to `HEAD`, 204, 304) cannot contradict it: a HEAD
response advertises the handler's `Content-Length`.
-/

/--
Steps `machine` until it halts. Returns everything it wrote and every event it emitted, or `none`
if it has not halted after 16 steps.
-/
def runToHalt (machine : Machine dir) : Option (String × Array (Event dir)) := Id.run do
  let mut machine := machine
  let mut out := ""
  let mut events := #[]
  for _ in [0:16] do
    let (next, step) := machine.step
    machine := next
    out := out ++ String.fromUTF8! step.output.toByteArray
    events := events ++ step.events
    if machine.halted then return some (out, events)
  return none

/-- A server machine that has read `request`. -/
def server (request : String) : Machine .receiving :=
  (({ config := {} } : Machine .receiving).feed request.toUTF8).step.1

def headers (fields : List (Header.Name × String)) : Headers :=
  fields.foldl (fun hs (name, value) => hs.insert name (Header.Value.ofString! value)) .empty

def get : String := "GET / HTTP/1.1\r\nHost: a\r\n\r\n"

def abc : Array Chunk := #[Chunk.ofByteArray "abc".toUTF8]

/-- Runs `machine` to a halt and checks that it answered 500 without writing the body. -/
def expect500 (name : String) (machine : Machine .receiving) : IO Unit := do
  let some (out, events) := runToHalt (machine.sendData abc |>.userClosedBody)
    | throw <| IO.userError s!"[{name}] the server never halted"
  unless out.startsWith "HTTP/1.1 500 Internal Server Error\r\n" &&
      out.contains "Content-Length: 0\r\n" && out.contains "Connection: close\r\n" &&
      !out.contains "abc" do
    throw <| IO.userError s!"[{name}] expected an empty 500, got:\n{out.quote}"
  unless events.any (· matches .failed .badMessage) do
    throw <| IO.userError s!"[{name}] no failure reported: {repr events}"

/-- Runs `machine` to a halt and returns its output, failing on a reported failure. -/
def expectOk (name : String) (machine : Machine .receiving) : IO String := do
  let some (out, events) := runToHalt machine
    | throw <| IO.userError s!"[{name}] the server never halted"
  if events.any (· matches .failed _) then
    throw <| IO.userError s!"[{name}] unexpected failure: {repr events}\n{out.quote}"
  return out

#eval runGroup "server machine: contradictory framing" do
  -- A streamed body with a handler's `Content-Length`.
  expect500 "chunked body, Content-Length: 3" <| server get
    |>.setKnownSize .chunked
    |>.send { status := .ok, headers := headers [(Header.Name.contentLength, "3")] }

  -- An empty body with a handler's `Content-Length`.
  expect500 "empty body, Content-Length: 1234" <| server get
    |>.setKnownSize (.fixed 0)
    |>.send { status := .ok, headers := headers [(Header.Name.contentLength, "1234")] }

  -- Framing fields that describe no length.
  let both := headers [(Header.Name.contentLength, "3"), (Header.Name.transferEncoding, "chunked")]
  expect500 "Content-Length with Transfer-Encoding" <| server get
    |>.send { status := .ok, headers := both }

  -- Control: matching framing writes the response.
  let out ← expectOk "matching Content-Length" <| server
      "GET / HTTP/1.1\r\nHost: a\r\nConnection: close\r\n\r\n"
    |>.setKnownSize (.fixed 3)
    |>.send { status := .ok, headers := headers [(Header.Name.contentLength, "3")] }
    |>.sendData abc |>.userClosedBody
  unless out.startsWith "HTTP/1.1 200 OK\r\n" && out.endsWith "\r\n\r\nabc" do
    throw <| IO.userError s!"matching Content-Length: got\n{out.quote}"

#eval runGroup "server machine: bodyless responses keep the handler's length" do
  let head := "HEAD / HTTP/1.1\r\nHost: a\r\nConnection: close\r\n\r\n"
  for size in [Body.Length.chunked, .fixed 0] do
    let out ← expectOk s!"HEAD, {repr size}" <| server head
      |>.setKnownSize size
      |>.send { status := .ok, headers := headers [(Header.Name.contentLength, "1234")] }
    unless out.startsWith "HTTP/1.1 200 OK\r\n" && out.contains "Content-Length: 1234\r\n" &&
        !out.contains "Transfer-Encoding" do
      throw <| IO.userError s!"HEAD, {repr size}: expected Content-Length: 1234, got\n{out.quote}"

  let close := "GET / HTTP/1.1\r\nHost: a\r\nConnection: close\r\n\r\n"
  for status in [Status.noContent, .notModified] do
    let out ← expectOk s!"{status}" <| server close
      |>.setKnownSize (.fixed 0)
      |>.send { status, headers := headers [(Header.Name.contentLength, "9")] }
    unless out.startsWith s!"HTTP/1.1 {status.toCode} " && !out.contains "Content-Length" do
      throw <| IO.userError s!"{status}: expected no framing fields, got\n{out.quote}"

#eval show IO Unit from do
  -- Client side: a request declaring 10 bytes for a 3-byte body ends the exchange unwritten.
  let request : Request.Head :=
    (Request.new |>.method .put |>.uri! "/upload" |>.header! "Host" "example.com"
      |>.header! "Content-Length" "10").line
  let machine := ({ config := {} } : Machine .sending)
    |>.setKnownSize (.fixed 3)
    |>.send request
    |>.sendData abc |>.userClosedBody
  let some (out, events) := runToHalt machine
    | throw <| IO.userError "the client never halted"
  unless out.isEmpty && events.any (· matches .failed .badMessage) do
    throw <| IO.userError s!"client: expected a failure and no output, got {repr events}\n{out.quote}"

#eval runGroup "server: handler framing contradicts its body" do
  checkTimed "streamed body with Content-Length: 3"
    (raw := get)
    (handler := fun _ => Response.ok |>.header! "Content-Length" "3"
      |>.stream fun s => s.send (Chunk.ofByteArray "abc".toUTF8))
    (expect := fun r => do
      assertStatus r "HTTP/1.1 500 Internal Server Error"
      assertAbsent r "abc")

  checkTimed "empty body with Content-Length: 1234"
    (raw := get)
    (handler := fun _ => Response.ok |>.header! "Content-Length" "1234" |>.text "")
    (expect := (assertStatus · "HTTP/1.1 500 Internal Server Error"))

  -- The 500 closes the connection, so a pipelined request gets no answer.
  checkTimed "pipelined request after the 500"
    (raw := get ++ get)
    (handler := fun _ => Response.ok |>.header! "Content-Length" "1234" |>.text "")
    (expect := fun r => do
      let text := String.fromUTF8! r
      unless (text.splitOn "HTTP/1.1 ").length == 2 do
        throw <| IO.userError s!"expected exactly one response, got:\n{text.quote}")

  checkTimed "HEAD with a streamed body and Content-Length: 1234"
    (raw := "HEAD / HTTP/1.1\r\nHost: a\r\nConnection: close\r\n\r\n")
    (handler := fun _ => Response.ok |>.header! "Content-Length" "1234"
      |>.stream fun s => s.send (Chunk.ofByteArray "abc".toUTF8))
    (expect := fun r => do
      assertStatus r "HTTP/1.1 200 OK"
      assertContains r "Content-Length: 1234\r\n"
      assertAbsent r "abc")
