import Std.Internal.UV
import Std.Net.Addr

/-!
A program that exits with libuv operations still in flight: timers, signals, connects, accepts,
receives, a write and a half-close are all pending when the event loop stops, and must stay pending
without crashing the exit.

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

/--
Keeps `sockets` open until the event loop is torn down. A socket referenced only from `main`'s
locals is finalized when `main` returns, which closes it and settles its operations before teardown
starts. Here they are captured by a continuation of a timer promise that is still pending at exit,
which teardown keeps, continuations included, for the rest of the process. The continuation never
runs; if it did, its output would fail the test.
-/
def keepOpenUntilTeardown (sockets : Array TCP.Socket) : IO Unit := do
  let timer ← Timer.mk 3600000 false
  let fired ← timer.next
  discard <| IO.mapTask (fun _ => IO.println s!"kept {sockets.size} sockets") fired.result?

def expectPending {α : Type} (what : String) (p : IO.Promise α) : IO Unit := do
  if ← p.isResolved then
    throw <| IO.userError s!"{what} completed before exit, so the test no longer covers it"

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

  -- Connected pairs that stay open until teardown, so the walk meets an in-flight `recv?`, a write
  -- the peer never reads and a `uv_shutdown_t` queued behind it. Each write repeats one 64 KiB chunk
  -- to stay cheap. The `accept` wait is bounded in practice: the connect is to loopback and the
  -- backlog is larger than the number of outstanding connects.
  let chunk := ByteArray.mk (Array.replicate 65536 (0 : UInt8))
  let payload := Array.replicate 512 chunk
  for _ in [0:4] do
    let server ← TCP.Socket.new
    server.bind (lo 0)
    server.listen 16
    let port := portOf (← server.getSockName)
    let client ← TCP.Socket.new
    let connected ← client.connect (lo port)
    let accepted ← match (← server.accept).result?.get with
      | some (.ok accepted) => pure accepted
      | some (.error e) => throw e
      | none => throw <| IO.userError "accept promise was dropped"
    match connected.result?.get with
    | some (.ok ()) => pure ()
    | some (.error e) => throw e
    | none => throw <| IO.userError "connect promise was dropped"
    keepOpenUntilTeardown #[server, client, accepted]
    let recv ← client.recv? 1024
    -- How much loopback absorbs differs by platform (Windows completes a 32 MiB write), so writes
    -- are added until one stays queued.
    let mut send ← client.send payload
    for _ in [0:16] do
      IO.sleep 20
      if !(← send.isResolved) then break
      send ← client.send payload
    let shutdown ← client.shutdown
    IO.sleep 20
    expectPending "recv?" recv
    expectPending "send" send
    expectPending "shutdown" shutdown

def main : IO Unit := do
  startInflight
  IO.println "exiting"
