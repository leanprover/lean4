import Std.Internal.UV
import Std.Net.Addr

/-!
Regression guard for the libuv teardown walk running Lean code.

`lean_uv_*_shutdown` used to resolve promises and drop references from inside the `uv_walk`
callback. A `(sync := true)` continuation attached to such a promise then ran on the walking
thread; when it dropped the last reference to another handle, that handle's finalizer freed a
`uv_handle_t` still linked into the queue `uv_walk` was iterating, crashing the walk.

The listener is created first so it is walked first, and the socket the continuation owns is
created later so it is still ahead of the walk when the continuation runs.
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

  -- This closure is the sole owner of `socket`, `timer` and `datagram`, and runs synchronously on
  -- the thread that resolves `accepted` — the teardown thread, from inside the walk.
  BaseIO.chainTask (sync := true) accepted.result? fun _ => do
    let _ ← (socket.getSockName : IO _).toBaseIO
    let _ ← (timer.stop : IO _).toBaseIO
    let _ ← (datagram.getSockName : IO _).toBaseIO
    pure ()

  IO.println "exiting"
