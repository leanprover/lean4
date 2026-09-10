import Std.Internal.UV
import Std.Net.Addr

/-!
A program that exits with libuv operations still in flight: timers, signals, connects, accepts,
receives and a half-close are all pending when the event loop stops, and must stay pending without
crashing the exit.

Nothing here is expected to fail, so setup errors are deliberately *not* caught: a swallowed
`Socket.new` or `bind` would silently reduce this to a test of nothing. The one exception is guarded
narrowly and explained where it occurs.
-/

open Std.Internal.UV
open Std.Net

def lo (port : UInt16) : SocketAddress :=
  .v4 (SocketAddressV4.mk (.ofParts 127 0 0 1) port)

/--
TEST-NET-1 (RFC 5737), which is never routed. Whether a connect to it fails immediately or stays
pending depends on whether the host has a default route, so both outcomes have to be accepted; each
one still leaves the socket itself alive at exit.
-/
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

  -- SIGWINCH, which libuv accepts on every platform.
  for _ in [0:8] do
    let s ← Signal.mk 28 true
    discard <| s.next

  for _ in [0:30] do
    let s ← TCP.Socket.new
    try
      discard <| s.connect blackhole
    catch _ =>
      -- See `blackhole`: an immediate failure is one of the two valid outcomes.
      pure ()

  for _ in [0:15] do
    let s ← TCP.Socket.new
    s.bind (lo 0)
    s.listen 16
    discard <| s.accept

  for _ in [0:20] do
    let s ← UDP.Socket.new
    s.bind (lo 0)
    discard <| s.recv 1024

  -- A connected pair, so that the exit also leaves an in-flight `recv?` and a `uv_shutdown_t`.
  -- The `accept` wait is bounded in practice: the connect is to loopback and the backlog is larger
  -- than the number of outstanding connects.
  for _ in [0:8] do
    let server ← TCP.Socket.new
    server.bind (lo 0)
    server.listen 16
    let port := portOf (← server.getSockName)
    let client ← TCP.Socket.new
    discard <| client.connect (lo port)
    match (← server.accept).result?.get with
    | some (.ok accepted) =>
        discard <| accepted.recv? 1024
        discard <| client.shutdown
    | some (.error e) => throw e
    | none => throw <| IO.userError "accept promise was dropped"

def main : IO Unit := do
  startInflight
  IO.println "exiting"
