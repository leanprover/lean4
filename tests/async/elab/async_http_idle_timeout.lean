module

import Std.Http.Test.Helpers
public meta import Std.Http.Test.Helpers

/-!
Regression tests for #15041: idle HTTP connections close silently before the first request and
after a response, while a handler may run longer than the idle timeout.
-/

open Std.Async
open Std Http Internal Test

private def idleConfig : Config :=
  { defaultConfig with keepAliveTimeout := ⟨100, by decide⟩ }

private def checkIdleClose (name : String) (request : Option String) (handler : TestHandler)
    (expect : ByteArray → IO Unit) : IO Unit := runGroup name <| Async.block do
  let (client, server) ← Mock.new
  try
    if let some raw := request then
      client.send raw.toUTF8
    Async.race
      (do
        Std.Http.Server.serveConnection server handler idleConfig |>.run
        expect ((← client.recv?).getD .empty)
        unless (← client.getSendChan.isClosed) do
          throw <| IO.userError "server did not close the connection")
      (do
        sleep 2000
        throw <| IO.userError "idle connection did not close")
  finally
    client.close

#eval checkIdleClose "idle before the first request" none okHandler fun response =>
  assertExact response ""

#eval checkIdleClose "idle after a response" (some (mkGet)) okHandler fun response => do
  assertStatus response "HTTP/1.1 200"
  assertResponseCount response 1
  assertContains response "ok"

#eval checkIdleClose "handler outlives the idle timeout" (some (mkGet))
    (fun _ => do
      sleep 300
      Response.ok |>.text "ok") fun response => do
  assertStatus response "HTTP/1.1 200"
  assertResponseCount response 1
  assertContains response "ok"
