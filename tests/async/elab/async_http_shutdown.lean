import Std.Http.Test.Helpers
import Std.Net.Addr

open Std.Async
open Std Http Internal Test
open Std.Net

/-!
Shutting down while a request handler is still running. The connection must answer the in-flight
request with `503 Service Unavailable` and finish promptly, including when the handler blocks its
thread or only returns after it has seen the cancellation.
-/

/-- Waits up to `ms` milliseconds for `task`, returning `none` on timeout. -/
def waitFor (task : Task α) (ms : Nat) : IO (Option α) := do
  for _ in [0:ms / 5] do
    if ← IO.hasFinished task then return some task.get
    IO.sleep 5
  if ← IO.hasFinished task then return some task.get
  return none

def assert503 (name : String) (response : String) : IO Unit := do
  unless response.startsWith "HTTP/1.1 503" do
    throw <| IO.userError s!"{name}: expected a 503 response, got {response.quote}"

/--
A handler built from a `started` promise it resolves once running and a `release` promise the test
resolves at the end, so a handler blocked on it can exit.
-/
abbrev ShutdownHandler := IO.Promise Unit → IO.Promise Unit → TestHandler

/-- Blocks its thread until the test releases it. -/
def blockingHandler : ShutdownHandler := fun started release _ => do
  started.resolve ()
  discard <| IO.wait release.result?
  Response.ok |>.text "late"

/-- Polls for cancellation without suspending, then answers. -/
def cooperativeHandler : ShutdownHandler := fun started _ _ => do
  started.resolve ()
  while !(← ContextAsync.isCancelled) do
    IO.sleep 1
  Response.ok |>.text "late"

/-- Suspends until cancelled, then answers. -/
def awaitingHandler : ShutdownHandler := fun started _ _ => do
  started.resolve ()
  ContextAsync.awaitCancellation
  Response.ok |>.text "late"

/--
Runs `serveConnection` on a mock transport for one GET, cancels the connection's context once the
handler has started, and returns the response.
-/
def shutdownMidRequest (name : String) (handler : ShutdownHandler) (ms : Nat := 2000) : IO String := do
  let (client, server) ← Mock.new
  let ctx ← CancellationContext.new
  let started ← IO.Promise.new
  let release ← IO.Promise.new
  try
    let conn ← EAsync.toBaseIO (ε := IO.Error) do
      client.send (mkGet "/").toUTF8
      Std.Http.Server.serveConnection server (handler started release) defaultConfig |>.runIn ctx

    let some _ ← waitFor started.result? ms
      | throw <| IO.userError s!"{name}: the handler never started"

    ctx.cancel .shutdown

    let some result ← waitFor conn ms
      | throw <| IO.userError s!"{name}: the connection did not finish within {ms} ms after shutdown"
    IO.ofExcept result

    let response ← client.tryRecv?
    return String.fromUTF8! (response.getD .empty)
  finally
    release.resolve ()

#eval do
  let response ← shutdownMidRequest "blocking_handler" blockingHandler
  assert503 "blocking_handler" response

-- The handler's response is ready by the time the connection notices the cancellation, so a fair
-- choice between the two would answer "late" about half of the time.
#eval do
  for _ in [0:20] do
    let response ← shutdownMidRequest "cooperative_handler" cooperativeHandler
    assert503 "cooperative_handler" response

#eval do
  for _ in [0:20] do
    let response ← shutdownMidRequest "awaiting_handler" awaitingHandler
    assert503 "awaiting_handler" response

/-- Reads from `client` until the peer closes the connection. -/
partial def readToEnd (client : TCP.Socket.Client) (acc : ByteArray := .empty) : Async ByteArray := do
  match ← client.recv? 4096 with
  | some chunk => readToEnd client (acc ++ chunk)
  | none => return acc

-- `Server.shutdownAndWait` waits for every connection, so a blocked handler must not hold it up.
#eval show IO Unit from do
  let name := "serve_blocking_handler"
  let started ← IO.Promise.new
  let release ← IO.Promise.new
  let handler : TestHandler := blockingHandler started release
  try
    let server ← Async.block <|
      Std.Http.Server.serve (SocketAddressV4.mk (.ofParts 127 0 0 1) 0) handler defaultConfig
    let some addr := server.localAddr
      | throw <| IO.userError s!"{name}: the server has no local address"

    let client ← TCP.Socket.Client.mk
    Async.block do
      client.connect addr
      client.send (mkGet "/").toUTF8

    let some _ ← waitFor started.result? 2000
      | throw <| IO.userError s!"{name}: the handler never started"

    let shutdown ← EAsync.toBaseIO server.shutdownAndWait
    let some result ← waitFor shutdown 2000
      | throw <| IO.userError s!"{name}: shutdown did not finish within 2000 ms while the handler was blocked"
    IO.ofExcept result

    let read ← EAsync.toBaseIO (readToEnd client)
    let some response ← waitFor read 2000
      | throw <| IO.userError s!"{name}: the connection was not closed within 2000 ms after shutdown"
    assert503 name (String.fromUTF8! (← IO.ofExcept response))
  finally
    release.resolve ()
