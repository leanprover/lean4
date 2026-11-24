import Std.Async
import Std.Internal.UV

open Std Async Internal.UV Net

/-!
Closing a TCP socket fails its pending operations with `EBADF`, not with the canceled error, which
is reserved for operations cut short because the program is finishing.

Once `main` returns, every pending libuv operation fails with the canceled error so that its waiters
finish: a timer, an accept, a `Child.wait`, a select on a sleep, and a send to a peer that does not
read, after the 2 s flush. The promise of `Timer.next` resolves instead, and that of `Signal.next`
stays pending, so that `result!` on them does not block finalization. DNS lookups still in flight
when `main` returns must not crash the program. A spawn started afterwards
fails at once, `kill` still works and `Loop.alive` is `false`.

On Windows the OS may take a whole write, and the shutdown behind it, into its buffers and complete
them before the `close` or the end of `main`.
-/

def outcome (r : Except IO.Error α) : String :=
  match r with
  | .ok _ => "succeeded"
  | .error (.invalidArgument ..) => "invalid argument"
  | .error e => if e.isCanceled then "canceled" else toString e

/-- Prints `merged` for every outcome in `accepted`, which may differ between platforms. -/
def report (what : String) (r : Except IO.Error α) (accepted : List String := []) (merged := "") :
    IO Unit := do
  let o := outcome r
  IO.println s!"{what}: {if accepted.contains o then merged else o}"

def await (p : IO.Promise (Except IO.Error α)) : IO (Except IO.Error α) := do
  return (← IO.wait p.result?).getD (.error (.userError "dropped"))

def listener : IO TCP.Socket := do
  let server ← TCP.Socket.new
  server.bind <| SocketAddressV4.mk (.ofParts 127 0 0 1) 0
  server.listen 1
  return server

/-- A connected client and its peer, which never reads. -/
def connected : IO (TCP.Socket × TCP.Socket) := do
  let server ← listener
  let accepted ← server.accept
  let client ← TCP.Socket.new
  discard <| AsyncTask.ofPromise (← client.connect (← server.getSockName)) |>.block
  return (client, ← AsyncTask.ofPromise accepted |>.block)

/-- Most of it stays in flight, as the peer never reads. -/
def bigSend (client : TCP.Socket) : IO (IO.Promise (Except IO.Error Unit)) :=
  client.send #[ByteArray.mk (Array.replicate (64 * 1024 * 1024) 0)]

def closeFailsPending : IO Unit := do
  let (client, peer) ← connected
  let recv ← client.recv? 1024
  let send ← bigSend client
  let shutdown ← client.shutdown
  client.close
  report "close: recv" (← await recv)
  let windowsMayComplete := if System.Platform.isWindows then ["succeeded"] else []
  let merged := "succeeded or invalid argument"
  report "close: send" (← await send) ("invalid argument" :: windowsMayComplete) merged
  report "close: shutdown" (← await shutdown) ("invalid argument" :: windowsMayComplete) merged
  peer.close

def main : IO Unit := do
  closeFailsPending

  let timer ← (← Timer.mk 60000 false).nextResult
  let compatTimer ← (← Timer.mk 60000 false).next
  -- `result!` blocks the thread that drops the promise, so the promise must not be dropped.
  unless System.Platform.isWindows do
    let compatSignal ← (← Signal.mk 28 false).next
    discard <| IO.mapTask (sync := true) (fun _ => pure ()) compatSignal.result!
  let selected ← (do Selectable.one #[.case (← Sleep.mk 60000).selector pure] : Async Unit).asTask
  let accept ← (← listener).accept
  let (client, peer) ← connected
  let send ← bigSend client
  let child ← IO.Process.spawn { cmd := "sleep", args := #["5"] }
  -- Queued lookups are cancelled and running ones finish; none may complete after the task manager.
  for _ in [0:200] do
    discard <| Internal.UV.DNS.getAddrInfo "localhost" "80" 0

  discard <| IO.asTask (prio := .dedicated) do
    report "Child.wait" (← child.wait.toBaseIO)
    report "timer started before main returned" (← await timer)
    -- `result!` would block forever on a dropped promise.
    IO.wait compatTimer.result!
    IO.println "Timer.next started before main returned: resolved"
    report "accept" ((← await accept).map fun _ => ())
    report "select on a sleep" (← IO.wait selected)
    report "send" (← await send) ["canceled", "succeeded"] "finished"
    report "spawn after main returned" ((← (IO.Process.spawn { cmd := "sleep", args := #["1"] }).toBaseIO).map fun _ => ())
    -- No thread reaps the child any more, so killing it stays safe.
    report "kill after main returned" (← (child.kill).toBaseIO)
    IO.println s!"Loop.alive after main returned: {← Loop.alive}"
    peer.close
  IO.println "main returns"
