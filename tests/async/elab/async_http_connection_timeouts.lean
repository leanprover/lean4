module

import Std.Http.Test.Helpers
public meta import Std.Http.Test.Helpers

/-!
Tests the timeouts of a server connection: a request head that keeps arriving slowly is cut off at
the header deadline, a request body that stalls is answered with 408 and cancels the handler's
context with `.deadline`, a connection's own timeout leaves the context it is served in alone, and
cancelling that context answers a request in progress with 503. A response body may pause longer
than `lingeringTimeout`, since only waits on the client are timed. A timeout is reported once, named
after the wait that ran out, and a partial head pipelined after a request is bounded by
`headerTimeout`, not `keepAliveTimeout`.
-/

open Std.Async
open Std Http Internal Test

/--
Runs `action`, failing if it takes longer than `ms` milliseconds.
-/
private def within [Inhabited α] (name : String) (ms : Time.Millisecond.Offset) (action : Async α) :
    Async α :=
  Async.race action do
    sleep ms
    throw <| IO.userError s!"{name} did not finish within {ms} ms"

#eval runGroup "a head that keeps arriving is cut off at the header deadline" <| Async.block do
  let (client, server) ← Mock.new
  let cfg : Config := { defaultConfig with
    headerTimeout := 300
    lingeringTimeout := 5000
    keepAliveTimeout := ⟨5000, by decide⟩ }
  try
    client.send "GET / HTTP/1.1\x0d\n".toUTF8
    -- Each line arrives well within the other timeouts, so only the header deadline applies.
    let trickle ← async do
      for _ in *...40 do
        sleep 50
        try client.send "X-Pad: y\x0d\n".toUTF8 catch _ => break
    let start ← IO.monoMsNow
    within "the server" 1500 (Server.serveConnection server okHandler cfg |>.run)
    unless (← IO.monoMsNow) - start ≥ 300 do
      throw <| IO.userError "closed before the header deadline"
    await trickle
  finally
    client.close

#eval runGroup "a stalled body is answered with 408 and cancels the handler's context" <|
    Async.block do
  let (client, server) ← Mock.new
  let seen ← IO.Promise.new (α := Option CancellationReason)
  let handler : TestHandler := fun req => do
    try discard (req.body.readAll : ContextAsync String) catch _ => pure ()
    let ctx ← ContextAsync.getContext
    await (← ctx.done)
    seen.resolve (← ctx.getCancellationReason)
    Response.ok |>.text "late"
  let cfg : Config := { defaultConfig with lingeringTimeout := 300 }
  try
    client.send "POST / HTTP/1.1\x0d\nHost: x\x0d\nContent-Length: 10\x0d\n\x0d\nabc".toUTF8
    within "the server" 2000 (Server.serveConnection server handler cfg |>.run)
    assertStatus ((← client.recv?).getD .empty) "HTTP/1.1 408"
    let reason ← within "the handler" 2000 (await seen.result?)
    unless reason == some (some .deadline) do
      throw <| IO.userError s!"the handler's context was cancelled with {repr reason}"
  finally
    client.close

#eval runGroup "a connection's timeout does not cancel the context it is served in" <|
    Async.block do
  let (client, server) ← Mock.new
  let ctx ← CancellationContext.new
  let cfg : Config := { defaultConfig with headerTimeout := 200 }
  try
    client.send "GET / HTTP/1.1\x0d\n".toUTF8
    within "the server" 2000 ((Server.serveConnection server okHandler cfg).runIn ctx)
    if ← ctx.isCancelled then
      throw <| IO.userError "the serving context was cancelled"
  finally
    client.close
    ctx.cancel .cancel

#eval runGroup "cancelling the serving context answers a request in progress with 503" <|
    Async.block do
  let (client, server) ← Mock.new
  let ctx ← CancellationContext.new
  let slowHandler : TestHandler := fun _ => do
    sleep 5000
    Response.ok |>.text "late"
  try
    client.send (mkGet).toUTF8
    let serve ← async ((Server.serveConnection server slowHandler defaultConfig).runIn ctx)
    sleep 100
    ctx.cancel .shutdown
    within "the server" 2000 (await serve)
    assertStatus ((← client.recv?).getD .empty) "HTTP/1.1 503"
  finally
    client.close

/--
Serves `raw` with `onRequest` under `cfg`, then closes the client once the server ends, and returns
what the server wrote and every `onFailure` report.
-/
private def serveRecording (raw : String) (onRequest : TestHandler) (cfg : Config)
    (limit : Time.Millisecond.Offset := 3000) : IO (String × Array String) := Async.block do
  let (client, server) ← Mock.new
  let failures ← IO.mkRef #[]
  let handler : Server.StatelessHandler :=
    { onRequest, onFailure := fun e => failures.modify (·.push (toString e)) }
  try
    client.send raw.toUTF8
    within "the server" limit (Server.serveConnection server handler cfg |>.run)
    let out ← client.recv?
    return (String.fromUTF8! (out.getD .empty), ← failures.get)
  finally
    client.close

-- The handler may pause between chunks as long as it wants, as server-sent events and long polling
-- do. Only the waits on the client are timed.
#eval runGroup "a response body that pauses longer than lingeringTimeout completes" do
  for (label, raw) in [("Connection: close", mkGetClose "/"), ("HTTP/1.0", "GET / HTTP/1.0\x0d\n\x0d\n")] do
    let (out, failures) ← serveRecording raw
      (fun _ => Response.ok |>.stream fun s => do
        s.send (Chunk.ofByteArray "first".toUTF8)
        sleep 600
        s.send (Chunk.ofByteArray "second".toUTF8))
      { defaultConfig with lingeringTimeout := 200 }
    unless out.endsWith "second" || out.endsWith "0\x0d\n\x0d\n" do
      throw <| IO.userError s!"{label}: the response was cut:\n{out.quote}"
    unless out.contains "first" && out.contains "second" && failures.isEmpty do
      throw <| IO.userError s!"{label}: got failures {failures} and\n{out.quote}"

-- A timeout is one failure, named after the wait that ran out, and an idle connection that times
-- out is no failure at all.
#eval runGroup "a timeout is reported once" do
  for (label, raw, cfg, want) in [
      ("head", "GET / HTTP/1.1\x0d\nHost: a\x0d\n", { defaultConfig with headerTimeout := 200 },
        #["request header timeout"]),
      ("body", "POST / HTTP/1.1\x0d\nHost: a\x0d\nContent-Length: 10\x0d\n\x0d\nabc",
        { defaultConfig with lingeringTimeout := 200 }, #["request timeout"]),
      ("idle after a response", mkGet "/", { defaultConfig with keepAliveTimeout := ⟨200, by decide⟩ }, #[])
    ] do
    let (_, failures) ← serveRecording raw okHandler cfg
    unless failures == want do
      throw <| IO.userError s!"{label}: expected {want}, got {failures}"

-- A request head that arrived with the previous request starts its header deadline once that
-- request is answered, not the keep-alive timeout.
#eval runGroup "a partial head pipelined after a request is cut off at the header deadline" do
  let cfg : Config := { defaultConfig with headerTimeout := 200, keepAliveTimeout := ⟨5000, by decide⟩ }
  let start ← IO.monoMsNow
  let (out, failures) ← serveRecording (mkGet "/a" ++ "GET /b HTTP/1.1\x0d\nHost") okHandler cfg (limit := 2000)
  unless (← IO.monoMsNow) - start < 2000 && out.startsWith "HTTP/1.1 200" &&
      failures == #["request header timeout"] do
    throw <| IO.userError s!"expected the 200 and a header timeout, got failures {failures} and\n{out.quote}"
