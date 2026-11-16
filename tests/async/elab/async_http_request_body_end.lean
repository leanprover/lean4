import Std.Http
import Std.Http.Test.Helpers

open Std.Async
open Std Http Internal Test

/-!
Tests how the server ends the request body stream a handler reads.

A body that ends early, is malformed, exceeds `maxBodySize`, stalls, or is discarded because the
response was already written must end `req.body` with an error, never with a clean end-of-stream
that makes a partial body look complete. A handler whose response streams while it reads the request
must keep receiving the body, including when the response body is the request body itself, and a
handler that stops waiting for the body must not leave the connection loop blocked handing it over.
-/

def withTimeout {α : Type} (name : String) (ms : Nat) (action : IO α) : IO α := do
  let task ← IO.asTask action
  let rec loop : Nat → IO α
    | 0 => do
      IO.cancel task
      throw <| IO.userError s!"'{name}' timed out after {ms} ms"
    | n + 1 => do
      if (← IO.getTaskState task) == .finished then
        match ← IO.wait task with
        | .ok x => pure x
        | .error e => throw e
      else
        IO.sleep 10
        loop n
  loop ((ms + 9) / 10)

/-- Waits up to `ms` for `p`, returning `"no outcome"` if the handler never recorded one. -/
def awaitOutcome (p : IO.Promise String) (ms : Nat) : IO String := do
  let t := p.result?
  let mut waited := 0
  while !(← IO.hasFinished t) && waited < ms do
    IO.sleep 10
    waited := waited + 10
  let outcome := if ← IO.hasFinished t then t.get.getD "dropped" else "no outcome"
  -- Keeps the promise alive until here, so dropping it cannot resolve the task.
  p.resolve "unused"
  return outcome

/-- How a handler reads its request body. -/
inductive ReadMode where
  | asyncReadAll
  | contextReadAll
deriving Repr

def readBody (mode : ReadMode) (body : Body.Stream) : ContextAsync String := do
  try
    let bytes : ByteArray ←
      match mode with
      | .asyncReadAll => (body.readAll : Async ByteArray)
      | .contextReadAll => body.readAll
    pure s!"ok {String.fromUTF8! bytes}"
  catch _ =>
    pure "error"

def readAllAsync (body : Body.Stream) : Async String := do
  try
    let bytes : ByteArray ← body.readAll
    pure s!"ok {String.fromUTF8! bytes}"
  catch _ =>
    pure "error"

/--
Sends `raw`, optionally closes the client's side, and serves the connection with a handler that
reads the whole request body. Returns the status line and what the handler's read returned.
-/
def runRead (name : String) (raw : String) (mode : ReadMode)
    (config : Config := defaultConfig) (closeInput : Bool := true) : IO (String × String) := do
  let outcome : IO.Promise String ← IO.Promise.new
  let handler : TestHandler := fun req => do
    outcome.resolve (← readBody mode req.body)
    Response.ok |>.text "done"
  let response ← withTimeout name 5000 <| Async.block do
    let (client, server) ← Mock.new
    client.send raw.toUTF8
    if closeInput then client.getSendChan.close
    Std.Http.Server.serveConnection server handler config |>.run
    pure ((← client.recv?).getD .empty)
  let status := (String.fromUTF8! response).splitOn "\x0d\n" |>.headD ""
  return (status, ← awaitOutcome outcome 2000)

def expectRead (name : String) (raw : String) (status : String) (outcome : String)
    (config : Config := defaultConfig) (closeInput : Bool := true) : IO Unit := do
  for mode in [ReadMode.asyncReadAll, .contextReadAll] do
    let (gotStatus, gotOutcome) ← runRead name raw mode config closeInput
    unless gotStatus == status && gotOutcome == outcome do
      throw <| IO.userError
        s!"'{name}' ({repr mode}): expected {status.quote} / {outcome.quote}, got {gotStatus.quote} / {gotOutcome.quote}"

def postHead (length : Nat) : String :=
  s!"POST / HTTP/1.1\x0d\nHost: x\x0d\nConnection: close\x0d\nContent-Length: {length}\x0d\n\x0d\n"

def chunkedHead : String :=
  "POST / HTTP/1.1\x0d\nHost: x\x0d\nConnection: close\x0d\nTransfer-Encoding: chunked\x0d\n\x0d\n"

-- A complete body reads back whole.
#eval expectRead "complete fixed body" (postHead 10 ++ "0123456789") "HTTP/1.1 200 OK" "ok 0123456789"
#eval expectRead "complete chunked body" (chunkedHead ++ "5\x0d\nhello\x0d\n0\x0d\n\x0d\n")
  "HTTP/1.1 200 OK" "ok hello"
#eval expectRead "empty fixed body" (postHead 0) "HTTP/1.1 200 OK" "ok "

-- A body that ends early or breaks its framing ends the handler's read with an error.
#eval expectRead "fixed body cut short by EOF" (postHead 10 ++ "12345")
  "HTTP/1.1 400 Bad Request" "error"
#eval expectRead "chunked body without its last chunk" (chunkedHead ++ "5\x0d\nhello\x0d\n")
  "HTTP/1.1 400 Bad Request" "error"
#eval expectRead "chunked body cut inside a chunk" (chunkedHead ++ "a\x0d\nhello")
  "HTTP/1.1 400 Bad Request" "error"
#eval expectRead "malformed second chunk size" (chunkedHead ++ "5\x0d\nhello\x0d\nzz\x0d\n")
  "HTTP/1.1 400 Bad Request" "error"
#eval expectRead "chunked body over maxBodySize"
  (chunkedHead ++ "5\x0d\nhello\x0d\n10\x0d\n0123456789abcdef\x0d\n0\x0d\n\x0d\n")
  "HTTP/1.1 413 Payload Too Large" "error" (config := { defaultConfig with maxBodySize := 12 })
#eval expectRead "body that stalls until the lingering timeout" (postHead 10 ++ "12345")
  "HTTP/1.1 408 Request Timeout" "error"
  (config := { defaultConfig with lingeringTimeout := 200 }) (closeInput := false)

/--
Serves `head`, then sends `body` 200 ms later, with `handler`. Returns the raw response.
-/
def serveWithLateBody (name : String) (head body : String) (handler : TestHandler) : IO String := do
  let response ← withTimeout name 5000 <| Async.block do
    let (client, server) ← Mock.new
    client.send head.toUTF8
    background do
      sleep 200
      client.send body.toUTF8
    Std.Http.Server.serveConnection server handler defaultConfig |>.run
    let mut acc := ByteArray.empty
    repeat
      match ← client.tryRecv? with
      | some bytes => acc := acc ++ bytes
      | none => break
    pure acc
  return String.fromUTF8! response

def expectSuffix (name : String) (response : String) (suffix : String) : IO Unit := do
  unless response.endsWith suffix do
    throw <| IO.userError s!"'{name}': expected the response to end with {suffix.quote}, got {response.quote}"

-- A streamed response whose producer reads the request body receives the whole body, even when the
-- body arrives after the response head was sent.
#eval do
  let handler : TestHandler := fun req =>
    Response.ok |>.stream fun out => do
      let body ← readAllAsync req.body
      out.send (Chunk.ofByteArray body.toUTF8)
  let response ← serveWithLateBody "streamed echo" (postHead 10) "0123456789" handler
  expectSuffix "streamed echo" response "d\x0d\nok 0123456789\x0d\n0\x0d\n\x0d\n"

-- The request body itself can be the response body.
#eval do
  let handler : TestHandler := fun req =>
    pure ((Response.ok |>.body req.body : Response Body.Stream) : Response Body.Any)
  let response ← serveWithLateBody "request body as response body" (postHead 10) "0123456789" handler
  expectSuffix "request body as response body" response "Content-Length: 10\x0d\n\x0d\n0123456789"

-- A body discarded because the response was already written ends the handler's later read with an
-- error rather than an empty body.
#eval show IO Unit from do
  let outcome : IO.Promise String ← IO.Promise.new
  let handler : TestHandler := fun req => do
    discard <| (async (do outcome.resolve (← readAllAsync req.body)) : Async (AsyncTask Unit))
    Response.ok |>.text "accepted"
  let response ← serveWithLateBody "read after the response" (postHead 10) "0123456789" handler
  expectSuffix "read after the response" response "accepted"
  let got ← awaitOutcome outcome 2000
  unless got == "error" do
    throw <| IO.userError s!"'read after the response': expected the read to fail, got {got.quote}"

-- A handler that waits for the first body chunk in a select and gives up at once still gets its
-- response written, whichever case wins.
#eval withTimeout "select read that gives up" 20000 do
  let handler : TestHandler := fun req => do
    let got ← Selectable.one #[
      .case req.body.recvSelector (fun chunk => pure chunk.isSome),
      .case (← Selector.sleep 0) (fun _ => pure false)]
    Response.ok |>.text (if got then "got" else "gave up")
  for i in [0:30] do
    let response ← withTimeout s!"select read that gives up, run {i}" 2000 <| Async.block do
      let (client, server) ← Mock.new
      client.send (mkPost "/" "0123456789" "Connection: close\x0d\n").toUTF8
      Std.Http.Server.serveConnection server handler defaultConfig |>.run
      pure ((← client.recv?).getD .empty)
    let text := String.fromUTF8! response
    unless text.startsWith "HTTP/1.1 200 OK" do
      throw (IO.userError s!"run {i}: unexpected response {text.quote}")
