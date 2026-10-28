import Std.Async
import Std.Sync.Channel

open Std Async

/-!
Benchmarks `Selectable.one` in the shape of the HTTP server's connection poll (#14246): every poll
races a cancellation context, the socket (here a channel), a freshly created sleep timer and the
handler's response channel.

- `random_bytes`: `IO.getRandomBytes 8`, which used to seed every selection. `Selectable.one` now
  seeds from `IO.stdGenRef`; this guards the per-call cost of `IO.getRandomBytes` itself.
- `poll_ready`: the data channel already holds a value, so the poll resolves through `tryFn`.
- `poll_pingpong`: a worker thread answers each request, which is only sent once the poll has
  registered its waiters, so every poll takes the registration slow path.
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
Receives the reply to `request` from `replies`, sending `request` only once a waiter is registered,
so the reply can never be ready when `tryFn` runs.
-/
def replyAfterRegister (requests replies : Std.Channel Nat) (request : Nat) : Selector Nat :=
  let inner := replies.recvSelector
  { tryFn := inner.tryFn
    registerFn := fun waiter => do
      inner.registerFn waiter
      discard <| requests.send request
    unregisterFn := inner.unregisterFn }

@[noinline]
def benchPollPingPong (iters : Nat) : IO Nat := do
  let requests : Std.Channel Nat ← Std.Channel.new
  let replies : Std.Channel Nat ← Std.Channel.new
  let worker ← BaseIO.asTask (prio := .dedicated) do
    for _ in *...iters do
      let v ← requests.sync.recv
      replies.sync.send v
  let acc ← Async.block do
    let ctx ← CancellationContext.new
    let idle ← Std.Channel.new
    let mut acc := 0
    for i in *...iters do
      acc := acc + (← poll ctx (replyAfterRegister requests replies (i + 1)) idle)
    return acc
  IO.wait worker
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
  run "random_bytes" (iters * 8) (benchRandomBytes iters)
  run "poll_ready" (iters * (iters + 1) / 2) (benchPollReady iters)
  -- Thread wake-ups make this scenario noisy, so it is kept small next to the deterministic ones.
  let pings := iters / 20 + 1
  run "poll_pingpong" (pings * (pings + 1) / 2) (benchPollPingPong pings)
