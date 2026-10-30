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

-- Part of the next request arrived with the previous one, so the connection is not idle: the header
-- timeout applies instead of the much longer keep-alive timeout.
#eval runGroup "pipelined request received in part" <| Async.block do
  let (client, server) ← Mock.new
  let config := { defaultConfig with keepAliveTimeout := ⟨5000, by decide⟩, headerTimeout := 100 }
  try
    client.send (mkGet ++ "GET / HTTP/1.1\x0d\nHo").toUTF8
    Async.race
      (do
        Std.Http.Server.serveConnection server okHandler config |>.run
        let response := (← client.recv?).getD .empty
        assertStatus response "HTTP/1.1 200"
        assertResponseCount response 1)
      (do
        sleep 2000
        throw <| IO.userError "the partial request was not timed out by the header timeout")
  finally
    client.close

-- The header timeout of a pipelined request counts from when its own head started arriving, not
-- from when the previous one did.
#eval runGroup "pipelined request after a slow head" <| Async.block do
  let (client, server) ← Mock.new
  let config := { defaultConfig with keepAliveTimeout := ⟨5000, by decide⟩, headerTimeout := 400 }
  try
    let serve ← async (t := AsyncTask) (Std.Http.Server.serveConnection server okHandler config |>.run)
    sleep 20
    client.send "GET / HTTP/1.1\x0d\n".toUTF8
    sleep 300
    client.send "Host: example.com\x0d\n\x0d\nGET / HTTP/1.1\x0d\n".toUTF8
    sleep 200
    try client.send "Host: example.com\x0d\nConnection: close\x0d\n\x0d\n".toUTF8
    catch _ => throw <| IO.userError "the second request timed out with the first one's deadline"
    Async.race (await serve) (do
      sleep 2000
      throw <| IO.userError "the connection did not finish")
    assertResponseCount ((← client.recv?).getD .empty) 2
  finally
    client.close

#eval checkIdleClose "handler outlives the idle timeout" (some (mkGet))
    (fun _ => do
      sleep 300
      Response.ok |>.text "ok") fun response => do
  assertStatus response "HTTP/1.1 200"
  assertResponseCount response 1
  assertContains response "ok"
