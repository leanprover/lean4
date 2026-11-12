import Std.Http
import Std.Http.Test.Helpers
import Std.Net.Addr

open Std.Async
open Std Http Internal Test
open Std.Net

/-!
Tests the end of connections and servers:
- a response body a handler returns after its connection ended is closed, so a producer streaming
  into it does not block forever;
- every `waitShutdown`, including one that starts after the server shut down, returns once the
  server is down;
- a `Handler.onFailure` that throws does not skip the connection's cleanup.
-/

def withTimeout {α : Type} (name : String) (ms : Nat) (action : IO α) : IO α := do
  let task ← IO.asTask action
  let rec loop : Nat → IO α
    | 0 => do
      IO.cancel task
      throw <| IO.userError s!"'{name}' did not finish within {ms} ms"
    | n + 1 => do
      if (← IO.getTaskState task) == .finished then
        match ← IO.wait task with
        | .ok x => pure x
        | .error e => throw e
      else
        IO.sleep 10
        loop n
  loop ((ms + 9) / 10)

/-- Waits up to `ms` for `p`, returning `"no outcome"` if nothing resolved it. -/
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

def within (ms : Nat) (action : Async Unit) : Async Bool :=
  Async.race (do action; pure true) (do sleep (.ofNat ms); pure false)

/--
Serves `raw` with a handler that reads the body, ignoring a failed read, then answers 500 ms later
with a streamed body. Cancels the connection's context after `shutdownAfter` ms, if given. Returns
the status line and what the response's producer saw.
-/
def lateResponse (name : String) (raw : String) (shutdownAfter : Option Nat) : IO (String × String) := do
  let outcome : IO.Promise String ← IO.Promise.new
  let handler : TestHandler := fun req => do
    try discard (req.body.readAll : Async ByteArray) catch _ => pure ()
    sleep 500
    Response.ok |>.stream fun out => do
      try
        out.send (Chunk.ofByteArray "late".toUTF8)
        outcome.resolve "sent"
      catch _ =>
        outcome.resolve "closed"
  let response ← withTimeout name 5000 <| Async.block do
    let (client, server) ← Mock.new
    let ctx ← CancellationContext.new
    client.send raw.toUTF8
    let serve ← async ((Std.Http.Server.serveConnection server handler
      { defaultConfig with lingeringTimeout := 200 }).runIn ctx)
    if let some ms := shutdownAfter then
      sleep (.ofNat ms)
      ctx.cancel .shutdown
    await serve
    pure ((← client.recv?).getD .empty)
  let status := (String.fromUTF8! response).splitOn "\x0d\n" |>.headD ""
  return (status, ← awaitOutcome outcome 3000)

-- The connection ends while the handler runs, by a stalled body or a shutdown; the handler then
-- returns a streamed body nobody will write. Its producer's send fails instead of waiting forever.
#eval show IO Unit from do
  for (name, raw, shutdownAfter, status) in [
      ("stalled body", "POST / HTTP/1.1\x0d\nHost: x\x0d\nContent-Length: 10\x0d\n\x0d\nabc", none,
        "HTTP/1.1 408 Request Timeout"),
      ("shutdown", mkPost "/" "0123456789", some 100, "HTTP/1.1 503 Service Unavailable")] do
    let (gotStatus, outcome) ← lateResponse name raw shutdownAfter
    unless gotStatus == status && outcome == "closed" do
      throw <| IO.userError
        s!"'{name}': expected {status.quote} and the late producer's send to fail, got {gotStatus.quote} / {outcome.quote}"

-- Two tasks wait for shutdown while a third shuts the server down; a wait that starts afterwards
-- returns at once.
#eval withTimeout "waitShutdown" 15000 <| Async.block do
  let server ← Server.serve (SocketAddressV4.mk (.ofParts 127 0 0 1) 0) okHandler defaultConfig
  let first ← async server.waitShutdown
  let second ← async server.waitShutdown
  sleep 50
  unless ← within 3000 server.shutdownAndWait do
    throw (IO.userError "shutdownAndWait did not return")
  unless ← within 3000 (await first) do
    throw (IO.userError "the first waitShutdown did not return")
  unless ← within 3000 (await second) do
    throw (IO.userError "the second waitShutdown did not return")
  unless ← within 3000 server.waitShutdown do
    throw (IO.userError "a waitShutdown after shutdownAndWait did not return")

/--
Serves `raw` with a handler whose failure callback throws, and returns the response and whether the
transport was closed. Fails if `serveConnection` throws.
-/
def serveWithThrowingLogger (name : String) (raw : String) (config : Config) : IO (String × Bool) := do
  let handler := Server.Handler.ofFns
    (fun req => do
      try discard (req.body.readAll : Async ByteArray) catch _ => pure ()
      Response.ok |>.text "ok")
    (onFailure := fun e => throw (IO.userError s!"logger failed on: {e}"))
  withTimeout name 5000 <| Async.block do
    let (client, server) ← Mock.new
    client.send raw.toUTF8
    try
      Std.Http.Server.serveConnection server handler config |>.run
    catch e =>
      throw (IO.userError s!"'{name}': serveConnection threw: {e}")
    pure (String.fromUTF8! ((← client.recv?).getD .empty), ← client.getRecvChan.isClosed)

-- A timeout fires and the failure callback throws: the connection still ends normally, writes what
-- it would have written, and closes the transport.
#eval show IO Unit from do
  let (_, closed) ← serveWithThrowingLogger "header timeout" "GET / HTTP/1.1\x0d\nHost: a\x0d\n"
    { defaultConfig with headerTimeout := 200 }
  unless closed do
    throw (IO.userError "'header timeout': the transport was not closed")
  let (response, closed) ← serveWithThrowingLogger "stalled body"
    "POST / HTTP/1.1\x0d\nHost: a\x0d\nContent-Length: 10\x0d\n\x0d\nabc"
    { defaultConfig with lingeringTimeout := 200 }
  unless response.startsWith "HTTP/1.1 408" && closed do
    throw (IO.userError s!"'stalled body': expected a 408 and a closed transport, got {response.quote}, closed={closed}")
