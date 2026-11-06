import Std.Http.Test.Helpers

/-!
A transport whose write reports its error after a delay, like TCP: the failed write must be reported
once, the connection must close, and the handler of the pipelined `POST` behind it must not run.
Also covers a write that fails when it starts.
-/

open Std.Async
open Std Http Internal Test

structure FailingTransport where
  inner : Mock.Server
  later : Bool
  writes : IO.Ref Nat

instance : Transport FailingTransport where
  recv t expect := Transport.recv t.inner expect
  sendAll t data := do
    let n ← t.writes.modifyGet fun n => (n, n + 1)
    if n == 0 then
      if t.later then sleep 50
      throw <| IO.userError "write failed"
    Transport.sendAll t.inner data
  recvSelector t expect := Transport.recvSelector t.inner expect
  close t := Transport.close t.inner

def runFailing (later : Bool) : IO Unit := Async.block do
  let (client, server) ← Mock.new
  let transport : FailingTransport := { inner := server, later, writes := ← IO.mkRef 0 }
  let failures ← IO.mkRef (#[] : Array String)
  let ran ← IO.mkRef (#[] : Array String)
  let h : Server.StatelessHandler := {
    onRequest := fun req => do
      let uri := toString req.line.uri
      unless uri == "/first" do ran.modify (·.push uri)
      Response.ok |>.text uri
    onFailure := fun e => failures.modify (·.push (toString e))
  }
  client.send (mkGet "/first" ++ mkPost "/second" "side effect" ++ mkGetClose "/third").toUTF8
  Async.race
    (Server.serveConnection transport h defaultConfig |>.run)
    (do sleep 5000; throw <| IO.userError "the connection did not close")
  unless (← ran.get).isEmpty do
    throw <| IO.userError s!"handlers ran after a failed write: {← ran.get}"
  unless (← failures.get) == #["write failed"] do
    throw <| IO.userError s!"expected one reported failure, got {← failures.get}"

#eval runGroup "write that fails later" (runFailing true)
#eval runGroup "write that fails when started" (runFailing false)
