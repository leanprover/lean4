import Std.Internal.UV
import Std.Net.Addr

/-!
`TCP.Socket.cancelAccept`, `TCP.Socket.cancelRecv` and `UDP.Socket.cancelRecv` drop the event loop's
reference to a pending promise, which can run a `(sync := true)` continuation inline. That used to
happen with the event loop lock held, so a continuation that blocks (such as a `Promise.result!`
waiter on the dropped promise) blocked every other use of the event loop. Each case below blocks
such a continuation and checks that a timer on another thread still fires. A watchdog exits the
process instead of hanging if it does not.
-/

open Std.Internal.UV Std.Net

def loopback (port : UInt16) : SocketAddress := .v4 (SocketAddressV4.mk (.ofParts 127 0 0 1) port)

def portOf : SocketAddress → UInt16
  | .v4 a => a.port
  | .v6 a => a.port

def waitFor (name what : String) (t : Task α) : IO Unit := do
  for _ in [0:200] do
    if ← IO.hasFinished t then return
    IO.sleep 50
  IO.println s!"{name}: timed out waiting for {what}"
  IO.Process.exit 1

/-- `arm` starts an operation and blocks a sync continuation on it until `gate` resolves. -/
def check (name : String) (arm : (started gate : IO.Promise Unit) → IO Unit) (cancel : IO Unit) :
    IO Unit := do
  let started ← IO.Promise.new
  let gate ← IO.Promise.new
  arm started gate
  let canceller ← IO.asTask (prio := .dedicated) cancel
  waitFor name "the continuation to start" started.result?
  let probe ← IO.asTask (prio := .dedicated) do
    let timer ← Timer.mk 1 false
    let fired ← timer.next
    let _ ← IO.wait fired.result?
  waitFor name "a timer while the continuation blocks" probe
  gate.resolve ()
  waitFor name "the cancel to return" canceller
  IO.println s!"{name}: ok"

def blockOn (task : Task α) (started gate : IO.Promise Unit) : BaseIO Unit :=
  BaseIO.chainTask (sync := true) task fun _ => do
    started.resolve ()
    -- Polls rather than `IO.wait`, which panics in a `sync` task.
    while !(← IO.hasFinished gate.result?) do
      IO.sleep 10

def main : IO Unit := do
  let listener ← TCP.Socket.new
  listener.bind (loopback 0)
  listener.listen 16
  check "TCP cancelAccept"
    (fun started gate => do blockOn (← listener.accept).result? started gate)
    listener.cancelAccept

  let port := portOf (← listener.getSockName)
  let client ← TCP.Socket.new
  let connected ← client.connect (loopback port)
  let some (.ok peer) := (← listener.accept).result?.get | throw (IO.userError "accept failed")
  let some (.ok ()) := connected.result?.get | throw (IO.userError "connect failed")
  check "TCP cancelRecv"
    (fun started gate => do blockOn (← client.recv? 64).result? started gate)
    client.cancelRecv
  -- Keeps the peer open until here; closing it would complete the receive instead.
  let _ ← peer.getSockName

  let udp ← UDP.Socket.new
  udp.bind (loopback 0)
  check "UDP cancelRecv"
    (fun started gate => do blockOn (← udp.recv 64).result? started gate)
    udp.cancelRecv
