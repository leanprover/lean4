import Std.Internal.UV
import Std.Net.Addr

/-!
Exercises libuv event-loop teardown (`finalize_libuv`) while operations are still
in flight.
-/

open Std.Internal.UV
open Std.Net

def lo (port : UInt16) : SocketAddress :=
  .v4 (SocketAddressV4.mk (.ofParts 127 0 0 1) port)

-- TEST-NET-1: unroutable: a connect to it stays pending forever.
def blackhole : SocketAddress :=
  .v4 (SocketAddressV4.mk (.ofParts 192 0 2 1) 80)

def portOf (a : SocketAddress) : UInt16 :=
  match a with
  | .v4 a => a.port
  | .v6 a => a.port

def startInflight : IO Unit := do
  for _ in [0:30] do
    let t ← Timer.mk 3600000 false
    discard <| t.next

  for _ in [0:8] do
    let s ← Signal.mk 28 true
    discard <| s.next

  for _ in [0:30] do
    let s ← TCP.Socket.new
    discard <| s.connect blackhole

  for _ in [0:15] do
    let s ← TCP.Socket.new
    try
      s.bind (lo 0)
      s.listen 16
      discard <| s.accept
    catch _ => pure ()

  for _ in [0:20] do
    let s ← UDP.Socket.new
    try
      s.bind (lo 0)
      discard <| s.recv 1024
    catch _ => pure ()

  for _ in [0:8] do
    let server ← TCP.Socket.new
    try
      server.bind (lo 0)
      server.listen 16
      let port := portOf (← server.getSockName)
      let client ← TCP.Socket.new
      discard <| client.connect (lo port)
      match (← server.accept).result?.get with
      | some (.ok accepted) =>
          discard <| accepted.recv? 1024
          discard <| client.shutdown
      | _ => pure ()
    catch _ => pure ()

#eval startInflight
