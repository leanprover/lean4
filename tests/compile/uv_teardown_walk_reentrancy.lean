import Std.Internal.UV
import Std.Net.Addr

/-!
The libuv teardown walk must not run Lean code.

Below, a `(sync := true)` continuation is the sole owner of three handles and hangs off a promise
still pending at exit. If the walk resolved or dropped that promise, the continuation would run on
the walking thread, and the finalizers of the handles it drops would free `uv_handle_t`s still
linked into the queue `uv_walk` iterates. Teardown keeps the promise instead, so the continuation
never runs; it prints if it does.
-/

open Std.Internal.UV Std.Net

def lo : SocketAddress := .v4 (SocketAddressV4.mk (.ofParts 127 0 0 1) 0)

def main : IO Unit := do
  let listener ← TCP.Socket.new
  listener.bind lo
  listener.listen 16
  let accepted ← listener.accept

  let socket ← TCP.Socket.new
  socket.bind lo
  let timer ← Timer.mk 100000 false
  let datagram ← UDP.Socket.new
  datagram.bind lo

  -- This closure is the sole owner of `socket`, `timer` and `datagram`.
  BaseIO.chainTask (sync := true) accepted.result? fun _ => do
    let _ ← (socket.getSockName : IO _).toBaseIO
    let _ ← (timer.stop : IO _).toBaseIO
    let _ ← (datagram.getSockName : IO _).toBaseIO
    let _ ← (IO.println "continuation ran" : IO _).toBaseIO
    pure ()

  IO.println "exiting"
