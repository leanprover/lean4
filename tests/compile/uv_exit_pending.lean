import Std.Async
import Std.Sync.Channel

/-!
A program that returns from `main` with libuv work still pending exits cleanly, and the teardown of
the event loop at exit runs no Lean code.

Pending at exit: timers, signals, connects, accepts on 64 listeners, receives, a write the peer never
reads, a half-close queued behind it, a select cycle, a detached retry loop's sleep, and timers whose
only reference is the loop's. The teardown drops each of these promises without running its
continuations: a continuation that runs prints, a `result!` that runs would panic and hang, a failing
sleep would make the retry loop spin forever, and a cycle left unreachable is a leak that leak checkers
report. The teardown also prints a warning if the loop does not close.

Exit still waits for running tasks with the loop up, so a task blocked on a timer wakes, and timer
finalizers racing the start of exit on worker threads are fine.
-/

open Std Async Std.Internal.UV Std.Net

def lo (port : UInt16) : SocketAddress :=
  .v4 (SocketAddressV4.mk (.ofParts 127 0 0 1) port)

/--
TEST-NET-1 (RFC 5737), which is never routed. Whether a connect to it fails immediately or stays
pending depends on whether the host has a default route, so both outcomes are accepted.
-/
def blackhole : SocketAddress :=
  .v4 (SocketAddressV4.mk (.ofParts 192 0 2 1) 80)

def portOf : SocketAddress → UInt16
  | .v4 a => a.port
  | .v6 a => a.port

/--
Keeps `sockets` open until the teardown: a continuation of a timer promise that is still pending at
exit captures them. It prints if it ever runs.
-/
def keepOpenUntilTeardown (sockets : Array TCP.Socket) : IO Unit := do
  let timer ← Timer.mk 3600000 false
  let fired ← timer.next
  discard <| IO.mapTask (fun _ => IO.println s!"kept {sockets.size} sockets") fired.result?

def expectPending {α : Type} (what : String) (p : IO.Promise α) : IO Unit := do
  if ← p.isResolved then
    throw <| IO.userError s!"{what} completed before exit, so the test no longer covers it"

def startHandles : IO Unit := do
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
      -- See `blackhole`.
      pure ()

  -- On Windows a closed listener delivers the aborted completions of its pending accepts before libuv
  -- releases it.
  let mut listeners := #[]
  for _ in [0:64] do
    let s ← TCP.Socket.new
    s.bind (lo 0)
    s.listen 16
    discard <| s.accept
    listeners := listeners.push s
  keepOpenUntilTeardown listeners

  for _ in [0:20] do
    let s ← UDP.Socket.new
    s.bind (lo 0)
    discard <| s.recv 1024

/--
Connected pairs that stay open until the teardown, with a pending `recv?`, a write the peer never
reads and a half-close queued behind it.
-/
def startStreams : IO Unit := do
  let chunk := ByteArray.mk (Array.replicate 65536 (0 : UInt8))
  let payload := Array.replicate 512 chunk
  for _ in [0:4] do
    let server ← TCP.Socket.new
    server.bind (lo 0)
    server.listen 16
    let client ← TCP.Socket.new
    let connected ← client.connect (lo (portOf (← server.getSockName)))
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
    -- How much loopback absorbs differs by platform, so writes are added until one stays queued.
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

/--
A `(sync := true)` continuation that is the only owner of three handles hangs off a promise still
pending at exit. If it ran, or were dropped before the loop is closed, it would release handles the
walk is still visiting.
-/
def startWalkReentrancy : IO Unit := do
  let listener ← TCP.Socket.new
  listener.bind (lo 0)
  listener.listen 16
  let accepted ← listener.accept
  let socket ← TCP.Socket.new
  socket.bind (lo 0)
  let timer ← Timer.mk 3600000 false
  let datagram ← UDP.Socket.new
  datagram.bind (lo 0)
  BaseIO.chainTask (sync := true) accepted.result? fun _ => do
    let _ ← (socket.getSockName : IO _).toBaseIO
    let _ ← (timer.stop : IO _).toBaseIO
    let _ ← (datagram.getSockName : IO _).toBaseIO
    let _ ← (IO.println "continuation ran" : IO _).toBaseIO
    pure ()

/-- A `result!` continuation would panic and then block if it ran once the teardown drops its promise. -/
def startResultBang : IO Unit := do
  let timer ← Timer.mk 3600000 false
  let fired ← timer.next
  discard <| IO.mapTask (fun (_ : Unit) => IO.println "fired") fired.result!

/-- The selector of `sleeper`, resolving `p` once it has registered and armed the timer. -/
def afterRegister (sleeper : Sleep) (p : IO.Promise Unit) : Selector Unit where
  tryFn := sleeper.selector.tryFn
  registerFn w := do
    sleeper.selector.registerFn w
    let sleepPromise ← sleeper.native.next
    BaseIO.chainTask (sync := true) sleepPromise.result? fun _ =>
      discard <| (IO.println "sleep promise settled" : IO Unit).toBaseIO
    p.resolve ()
  unregisterFn := sleeper.selector.unregisterFn

/-- A select whose waiters reference each other through the pending sleep promise. -/
def startPendingSelect : IO Unit := do
  Async.block do
    let registered ← IO.Promise.new
    let pending : Async Unit := do
      let ch ← Std.Channel.new (α := Nat)
      let sleeper ← Sleep.mk 3600000
      Selectable.one #[
        .case ch.recvSelector (fun _ => pure ()),
        .case (afterRegister sleeper registered) (fun _ => pure ())]
    discard <| pending.asTask
    Async.ofPurePromise (pure registered)

partial def heartbeat (retries : IO.Ref Nat) : Async Unit := do
  try
    sleep 1000
  catch _ =>
    retries.modify (· + 1)
  heartbeat retries

/-- A detached loop that retries on errors would spin if its pending sleep failed at exit. -/
def startRetryLoop : IO Unit := do
  let retries ← IO.mkRef 0
  discard <| (heartbeat retries).asTask
  IO.sleep 100

partial def churn (n : Nat) : IO Unit := do
  if n == 0 then return ()
  let mut ts := #[]
  for _ in [0:64] do
    let t ← Timer.mk 1 false
    let p ← t.next
    ts := ts.push (t, p)
  for (_, p) in ts do
    discard <| IO.wait p.result?
  churn (n - 1)

/--
Timers whose only reference is the loop's, finalized by the teardown, and tasks that keep dropping
fired timers while `main` returns, so that their finalizers race the start of exit.
-/
def startFinalizers : IO Unit := do
  for _ in [0:64] do
    let t ← Timer.mk 3600000 false
    discard <| t.next
  for _ in [0:8] do
    discard <| (churn 50).asTask

/-- Exit waits for this task with the loop still running, so its timer fires. -/
def startWaitingTask : IO Unit := do
  let timer ← Timer.mk 200 false
  let fired ← timer.next
  let started ← IO.Promise.new
  let _ ← IO.asTask do
    started.resolve ()
    let woke ← IO.wait fired.result?
    IO.println s!"woke: {woke.isSome}"
  discard <| IO.wait started.result?

def main : IO Unit := do
  startHandles
  startStreams
  startWalkReentrancy
  startResultBang
  startPendingSelect
  startRetryLoop
  startFinalizers
  startWaitingTask
  IO.println "exiting"
