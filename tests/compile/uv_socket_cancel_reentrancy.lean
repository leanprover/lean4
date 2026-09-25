import Std.Internal.UV
import Std.Net.Addr

/-!
`TCP.Socket.cancelAccept`, `TCP.Socket.cancelRecv` and `UDP.Socket.cancelRecv` drop the event
loop's reference to a pending promise. When that was the last reference, the promise resolves to
`none` and a `(sync := true)` continuation runs inline inside the cancel. The continuation here
re-enters the same cancel, which used to release the promise, the pending client or buffer, and the
socket a second time.

The UDP case did not crash before the fix, because `UDP.Socket.cancelRecv` also leaked a socket
reference that absorbed the extra release. It catches the old release order coming back without
that leak.
-/

open Std.Internal.UV Std.Net

def loopback (port : UInt16) : SocketAddress := .v4 (SocketAddressV4.mk (.ofParts 127 0 0 1) port)

def portOf : SocketAddress → UInt16
  | .v4 a => a.port
  | .v6 a => a.port

/-- The accept promise is not returned, so after this the loop holds its only reference. -/
def armAccept (listener : TCP.Socket) : IO Unit := do
  let accepted ← listener.accept
  BaseIO.chainTask (sync := true) accepted.result? fun _ => do
    let _ ← (listener.cancelAccept : IO _).toBaseIO

def armRecv (socket : TCP.Socket) : IO Unit := do
  let received ← socket.recv? 64
  BaseIO.chainTask (sync := true) received.result? fun _ => do
    let _ ← (socket.cancelRecv : IO _).toBaseIO

def cancelAcceptFromContinuation : IO Unit := do
  for _ in [0:200] do
    let listener ← TCP.Socket.new
    listener.bind (loopback 0)
    listener.listen 16
    armAccept listener
    listener.cancelAccept
    -- The listener must still be intact.
    let _ ← listener.getSockName

def cancelRecvFromContinuation : IO Unit := do
  let server ← TCP.Socket.new
  server.bind (loopback 0)
  server.listen 64
  let port := portOf (← server.getSockName)
  for _ in [0:200] do
    let client ← TCP.Socket.new
    let connected ← client.connect (loopback port)
    let some (.ok peer) := (← server.accept).result?.get | throw (IO.userError "accept failed")
    let some (.ok ()) := connected.result?.get | throw (IO.userError "connect failed")
    armRecv client
    client.cancelRecv
    let _ ← client.getSockName
    -- Keeps the peer open until here; closing it would complete the receive instead.
    let _ ← peer.getSockName

def armUdpRecv (socket : UDP.Socket) : IO Unit := do
  let received ← socket.recv 64
  BaseIO.chainTask (sync := true) received.result? fun _ => do
    let _ ← (socket.cancelRecv : IO _).toBaseIO

def udpCancelRecvFromContinuation : IO Unit := do
  for _ in [0:200] do
    let socket ← UDP.Socket.new
    socket.bind (loopback 0)
    armUdpRecv socket
    socket.cancelRecv
    let _ ← socket.getSockName

def main : IO Unit := do
  cancelAcceptFromContinuation
  IO.println "TCP cancelAccept ok"
  cancelRecvFromContinuation
  IO.println "TCP cancelRecv ok"
  udpCancelRecvFromContinuation
  IO.println "UDP cancelRecv ok"
