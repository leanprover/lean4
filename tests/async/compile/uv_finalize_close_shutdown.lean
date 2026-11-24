import Std.Async.Basic
import Std.Internal.UV

open Std Async Internal.UV Net

/-!
Closing a TCP socket while its shutdown is pending, as a connection handler does while `main`
returns, must not crash the program. Finalization skips closing handles, so `close` itself fails the
shutdown with `EBADF`: libuv may complete it only once the task manager is gone. The window is
narrow, so the parent runs the child up to 10 times and stops at its first failure.
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
  let go : IO.Promise Unit ← IO.Promise.new
  discard <| IO.asTask (prio := .dedicated) do
    discard <| IO.wait go.result?
    for client in clients do
      discard <| client.shutdown.toBaseIO
      client.close
  go.resolve ()
  -- Returns while the closes run, before the loop thread has finished them.
  let start ← IO.monoNanosNow
  while (← IO.monoNanosNow) - start < 400000 do pure ()
  IO.println "main returns"

def runs : Nat := 10

def main (args : List String) : IO Unit := do
  if args == ["child"] then
    child
    return
  let self := (← IO.appPath).toString
  for run in [1:runs+1] do
    let out ← IO.Process.output { cmd := self, args := #["child"] }
    if out.exitCode != 0 || out.stdout != "main returns\n" then
      IO.println s!"run {run} of {runs} ended with exit code {out.exitCode}"
      return
  IO.println "ok"
