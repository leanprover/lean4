import Std.Async.Basic
import Std.Internal.UV

open Std Async Internal.UV Net

/-!
Closing TCP sockets with pending shutdowns while `main` returns must not crash: `close` itself fails
the shutdown with `EBADF`, since libuv may complete it only once the task manager is gone. The
parent runs the child up to 10 times.
-/

def sockets : Nat := 100

def child : IO Unit := do
  let server ← TCP.Socket.new
  server.bind <| SocketAddressV4.mk (.ofParts 127 0 0 1) 0
  server.listen sockets.toUInt32
  let addr ← server.getSockName
  let mut clients := #[]
  let mut peers := #[]
  for _ in [0:sockets] do
    let accepted ← server.accept
    let client ← TCP.Socket.new
    discard <| AsyncTask.ofPromise (← client.connect addr) |>.block
    peers := peers.push (← AsyncTask.ofPromise accepted |>.block)
    clients := clients.push client
  discard <| IO.asTask (prio := .dedicated) do
    for client in clients do
      discard <| client.shutdown.toBaseIO
      client.close
  -- Returns while the closes run, before the loop thread has finished them.
  let start ← IO.monoNanosNow
  while (← IO.monoNanosNow) - start < 400000 do pure ()

def main (args : List String) : IO Unit := do
  if args == ["child"] then
    child
    return
  for run in [1:11] do
    let out ← IO.Process.output { cmd := (← IO.appPath).toString, args := #["child"] }
    if out.exitCode != 0 then
      IO.println s!"run {run} of 10 exited with {out.exitCode}"
      return
  IO.println "ok"
