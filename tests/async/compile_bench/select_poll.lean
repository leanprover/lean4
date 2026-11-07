import Std.Async
import Std.Sync.Channel

open Std Async

/-!
Benchmarks `Selectable.one` in the shape of the HTTP server's connection poll (#14246): every poll
races a cancellation context, the socket (here a channel), a freshly created sleep timer and the
handler's response channel. Arming and cancelling that timer wakes the libuv loop thread, as it
does in the server, so this file's instruction counts are noisier than those of single-threaded
benchmarks.

- `random_bytes`: `IO.getRandomBytes 8`, which used to seed every selection. `Selectable.one` now
  seeds from `IO.stdGenRef`; this guards the per-call cost of `IO.getRandomBytes` itself.
- `poll_ready`: the data channel already holds a value, so the poll resolves through `tryFn`.
- `poll_dispatch`: each reply comes from a task spawned once the poll has registered its waiters,
  as the server dispatches a request to its handler, so every poll takes the registration path.
-/

@[noinline]
def benchRandomBytes (iters : Nat) : IO Nat := do
  let mut acc := 0
  for _ in *...iters do
    acc := acc + (← IO.getRandomBytes 8).size
  return acc

/-- One server-shaped poll that resolves with the next value of `data`. -/
def poll (ctx : CancellationContext) (data : Selector Nat) (response : Std.Channel Nat) : Async Nat := do
  Selectable.one #[
    .case ctx.doneSelector (fun _ => pure 0),
    .case data pure,
    .case (← Selector.sleep 10000) (fun _ => pure 0),
    .case response.recvSelector pure
  ]

@[noinline]
def benchPollReady (iters : Nat) : IO Nat := Async.block do
  let ctx ← CancellationContext.new
  let data ← Std.Channel.new
  let response ← Std.Channel.new
  let mut acc := 0
  for i in *...iters do
    discard <| data.send (i + 1)
    acc := acc + (← poll ctx data.recvSelector response)
  return acc

/--
Receives `reply` from `replies`, but only spawns the task that sends it once a waiter is registered
(as `Server.Connection` dispatches handlers: `asTask`, then `chainTask` into a channel), so the reply
can never be ready when `tryFn` runs.
-/
def replyAfterRegister (replies : Std.Channel Nat) (reply : Nat) : Selector Nat :=
  let inner := replies.recvSelector
  { tryFn := inner.tryFn
    registerFn := fun waiter => do
      inner.registerFn waiter
      let handler ← BaseIO.asTask (pure reply)
      discard <| BaseIO.chainTask handler (discard ∘ replies.send)
    unregisterFn := inner.unregisterFn }

@[noinline]
def benchPollDispatch (iters : Nat) : IO Nat := Async.block do
  let ctx ← CancellationContext.new
  let replies ← Std.Channel.new
  let idle ← Std.Channel.new
  let mut acc := 0
  for i in *...iters do
    acc := acc + (← poll ctx (replyAfterRegister replies (i + 1)) idle)
  return acc

def run (name : String) (expected : Nat) (act : IO Nat) : IO Unit := do
  let t1 ← IO.monoNanosNow
  let acc ← act
  let t2 ← IO.monoNanosNow
  unless acc == expected do
    throw <| .userError s!"{name}: expected checksum {expected}, got {acc}"
  IO.println s!"measurement: {name} {(t2 - t1).toFloat / 1000000000.0} s"

def main (args : List String) : IO Unit := do
  let iters := args[0]!.toNat!
  -- System calls dominate `IO.getRandomBytes`, so fewer iterations give the same signal.
  run "random_bytes" ((iters / 4 + 1) * 8) (benchRandomBytes (iters / 4 + 1))
  run "poll_ready" (iters * (iters + 1) / 2) (benchPollReady iters)
  -- Spawning a task and arming a timer per poll make this path several times slower than the others.
  let dispatches := iters / 4 + 1
  run "poll_dispatch" (dispatches * (dispatches + 1) / 2) (benchPollDispatch dispatches)
