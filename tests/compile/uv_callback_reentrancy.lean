import Std.Internal.UV
import Std.Net.Addr

/-!
Regression guard for uv callbacks that keep using their handle after resolving its promise.

`handle_timer_event` resolved `m_promise` and only then read `timer->m_uv_timer` and released the
loop's reference. A `(sync := true)` continuation runs inside that resolve, on the loop thread; a
`cancel`/`stop` from it hands the loop's reference back, the continuation's own reference dies with
its closure, and the callback then dereferenced a freed `lean_uv_timer_object`.

The cancellation entry points had the mirror-image problem: they released the promise before
clearing the field it lives in, so a continuation resolved by that release saw a dangling
`m_promise`/`m_promise_accept`/`m_promise_read` and released it again.
-/

open Std.Internal.UV Std.Net

def lo : SocketAddress := .v4 (SocketAddressV4.mk (.ofParts 127 0 0 1) 0)

/-- Cancels the timer from inside its own firing callback. -/
def timerFromCallback : IO Unit := do
  for _ in [0:200] do
    let timer ← Timer.mk 1 false
    let fired ← timer.next
    BaseIO.chainTask (sync := true) fired.result? fun _ => do
      let _ ← (timer.cancel : IO _).toBaseIO
      let _ ← (timer.stop : IO _).toBaseIO
      pure ()
    let _ ← IO.wait fired.result?

/-- Re-enters the socket from the continuation that `cancelAccept` resolves. -/
def acceptFromCancel : IO Unit := do
  let arm (listener : TCP.Socket) : IO Unit := do
    let accepted ← listener.accept
    BaseIO.chainTask (sync := true) accepted.result? fun _ => do
      let _ ← (listener.accept : IO _).toBaseIO
      let _ ← (listener.cancelAccept : IO _).toBaseIO
      pure ()
  for _ in [0:200] do
    let listener ← TCP.Socket.new
    listener.bind lo
    listener.listen 16
    arm listener
    listener.cancelAccept

/-- Re-enters the socket from the continuation that `cancelRecv` resolves. -/
def recvFromCancel : IO Unit := do
  let arm (socket : UDP.Socket) : IO Unit := do
    let received ← socket.recv 64
    BaseIO.chainTask (sync := true) received.result? fun _ => do
      let _ ← (socket.recv 64 : IO _).toBaseIO
      let _ ← (socket.cancelRecv : IO _).toBaseIO
      pure ()
  for _ in [0:200] do
    let socket ← UDP.Socket.new
    socket.bind lo
    arm socket
    socket.cancelRecv

def main : IO Unit := do
  timerFromCallback
  acceptFromCancel
  recvFromCancel
  IO.println "exiting"
