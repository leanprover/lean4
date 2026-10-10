import Std.Async
import Std.Net.Addr

/-!
TCP and UDP `sendAll` deliver every buffer in order, both when the `uv_buf_t` array fits on the
stack and when it is large enough to be heap-allocated.
-/

open Std.Async
open Std.Net

def assertBEq [BEq α] [ToString α] (actual expected : α) : IO Unit := do
  unless actual == expected do
    throw <| IO.userError <|
      s!"expected '{expected}', got '{actual}'"

def chunks (n : Nat) : Array ByteArray :=
  (Array.range n).map fun i => s!"<{i}>".toUTF8

def concat (bufs : Array ByteArray) : ByteArray :=
  bufs.foldl (· ++ ·) .empty

def loopback : SocketAddress :=
  .v4 (SocketAddressV4.mk (.ofParts 127 0 0 1) 0)

def runAsync (x : Async α) : IO α := do
  (← x.toIO).block

partial def recvAll (client : TCP.Socket.Client) (acc : ByteArray) : Async ByteArray := do
  match ← client.recv? 65536 with
  | some data => recvAll client (acc ++ data)
  | none => return acc

def tcpSendAll (n : Nat) : IO Unit := do
  let server ← TCP.Socket.Server.mk
  server.bind loopback
  server.listen 128
  let addr ← server.getSockName

  let data := chunks n
  let sender ← (show Async Unit from do
    let client ← TCP.Socket.Client.mk
    client.connect addr
    client.sendAll data
    client.shutdown).toIO

  let received ← runAsync do
    let peer ← server.accept
    recvAll peer .empty

  sender.block
  assertBEq received.toList (concat data).toList

#eval tcpSendAll 1
#eval tcpSendAll 16
#eval tcpSendAll 17
#eval tcpSendAll 2000

def udpSendAll (n : Nat) (withAddr : Bool) : IO Unit := do
  let receiver ← UDP.Socket.mk
  receiver.bind loopback
  let addr ← receiver.getSockName

  let sender ← UDP.Socket.mk
  sender.bind loopback
  unless withAddr do
    sender.connect addr

  let data := chunks n
  runAsync <| sender.sendAll data (if withAddr then some addr else none)

  let (received, _) ← runAsync <| receiver.recv 65536
  assertBEq received.toList (concat data).toList

#eval udpSendAll 1 true
#eval udpSendAll 16 true
#eval udpSendAll 17 true
#eval udpSendAll 17 false
#eval udpSendAll 500 true
