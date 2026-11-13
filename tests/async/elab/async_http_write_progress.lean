import Std.Http.Test.Helpers

/-!
`Config.writeTimeout` bounds the time without a completed write, not the time until every write is
done: a peer that reads slowly but steadily gets the whole response, even when the next write is
always queued before the last one completes.
-/

open Std.Async
open Std Http Internal Test

/-- A transport whose every write takes `delay` milliseconds. -/
structure SlowTransport where
  inner : Mock.Server
  delay : Time.Millisecond.Offset

instance : Transport SlowTransport where
  sendAll t data := do
    sleep t.delay
    Transport.sendAll t.inner data
  recvSelector t expect := Transport.recvSelector t.inner expect
  close t := Transport.close t.inner

#eval runGroup "writes that each complete in time" do
  let (text, failures) ← Async.block do
    let (client, server) ← Mock.new
    let failures ← IO.mkRef (#[] : Array String)
    let handler : Server.StatelessHandler := {
      onRequest := fun _ => Response.ok |>.stream fun s => do
        for i in [0:20] do
          s.send (Chunk.ofByteArray s!"chunk {i}\n".toUTF8)
      onFailure := fun e => failures.modify (·.push (toString e))
    }
    client.send (mkGetClose "/").toUTF8
    -- Each write takes 600 ms, so the second one ends 1200 ms after the first started.
    Async.race
      (Server.serveConnection ({ inner := server, delay := 600 } : SlowTransport) handler
        { defaultConfig with writeTimeout := 1000 } |>.run)
      (do sleep 10000; throw <| IO.userError "the connection did not close")
    let mut out := ByteArray.empty
    repeat
      match ← client.tryRecv? with
      | some data => out := out ++ data
      | none => break
    return (String.fromUTF8! out, ← failures.get)
  unless failures.isEmpty do
    throw <| IO.userError s!"unexpected failures: {failures}"
  unless text.endsWith "chunk 19\n\x0d\n0\x0d\n\x0d\n" do
    throw <| IO.userError s!"expected the whole response:\n{text.quote}"
