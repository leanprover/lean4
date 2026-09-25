import Std.Internal.UV
import Std.Net.Addr

/-!
`UDP.Socket.cancelRecv` must release the reference that `recv` or `waitReadable` took for the
event loop. It used to keep it, so every cancelled receive leaked the socket and its file
descriptor. `Std.Async.UDP.Socket.recvSelector` cancels one whenever no datagram is ready yet.
-/

open Std.Internal.UV Std.Net

def loopback : SocketAddress := .v4 (SocketAddressV4.mk (.ofParts 127 0 0 1) 0)

def openFds : IO Nat :=
  return (← System.FilePath.readDir "/dev/fd").size

def main : IO Unit := do
  if System.Platform.isWindows then
    IO.println "ok"
    return
  let before ← openFds
  for _ in [0:256] do
    let socket ← UDP.Socket.new
    socket.bind loopback
    let _ ← socket.recv 64
    socket.cancelRecv
  let after ← openFds
  if after > before + 16 then
    IO.println s!"leaked {after - before} file descriptors"
  else
    IO.println "ok"
