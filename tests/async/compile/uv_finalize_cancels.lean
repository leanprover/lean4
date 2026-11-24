import Std.Async.Basic
import Std.Internal.UV

open Std Async Internal.UV Net

/-!
When `main` returns, `lean_finalize_task_manager` stops the event loop thread before it finalizes the
task manager, since a libuv callback that ran afterwards would resolve a promise through a task
manager that is gone. Every libuv operation still pending then fails with `UV_ECANCELED`, so that the
tasks waiting on it finish: a timer, an accept that never comes, a `Child.wait` on a child that keeps
running, and a send to a peer that does not read, which gets the 2 s flush first. An operation
started after `main` returned fails with `UV_ECANCELED` at once, and `Loop.alive` reports `false`.

The send stays in flight on Linux and macOS, so it is canceled there; Windows may take all of it
into its buffers and complete it before `main` returns. Either way it must finish.
-/

def report (what : String) (r : Except IO.Error α) : IO Unit := do
  let outcome := match r with
    | .ok _ => "succeeded"
    | .error e => if e.isCanceled then "canceled" else toString e
  IO.println s!"{what}: {outcome}"

def await (p : IO.Promise (Except IO.Error α)) : IO (Except IO.Error α) := do
  return (← IO.wait p.result?).getD (.error (.userError "dropped"))

def listener : IO TCP.Socket := do
  let server ← TCP.Socket.new
  server.bind <| SocketAddressV4.mk (.ofParts 127 0 0 1) 0
  server.listen 1
  return server

def main : IO Unit := do
  let timer ← (← Timer.mk 60000 false).nextResult

  let idle ← listener
  let accept ← idle.accept

  let server ← listener
  let accepted ← server.accept
  let client ← TCP.Socket.new
  discard <| AsyncTask.ofPromise (← client.connect (← server.getSockName)) |>.block
  let peer ← AsyncTask.ofPromise accepted |>.block
  -- The peer never reads, so most of this stays in flight.
  let send ← client.send #[ByteArray.mk (Array.replicate (64 * 1024 * 1024) 0)]

  let child ← IO.Process.spawn { cmd := "sleep", args := #["5"] }

  discard <| IO.asTask (prio := .dedicated) do
    report "Child.wait" (← child.wait.toBaseIO)
    report "timer started before main returned" (← await timer)
    report "accept" ((← await accept).map fun _ => ())
    -- Canceled when it stayed in flight, succeeded when the OS took all of it; never stuck.
    let sent ← await send
    match sent with
    | .ok _ => IO.println "send: finished"
    | .error e => if e.isCanceled then IO.println "send: finished" else report "send" sent
    report "timer started after main returned" (← (do (← Timer.mk 10 false).nextResult).toBaseIO)
    IO.println s!"Loop.alive after main returned: {← Loop.alive}"
    peer.close
  IO.println "main returns"
