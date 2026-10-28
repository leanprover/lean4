import Std.Async
import Std.Sync.Channel

open Std Async

/-!
Benchmarks `Selectable.one` in the shape of the HTTP server's connection poll (#14246): every poll
races a cancellation context, the socket (here a channel), a freshly created sleep timer and the
handler's response channel.

- `random_bytes`: `IO.getRandomBytes 8`, which used to seed every selection.
- `poll_ready`: the data channel already holds a value, so the poll resolves through `tryFn`.
- `poll_pingpong`: a worker thread answers each request after the poll has registered its waiters.
-/

@[noinline]
def benchRandomBytes (iters : Nat) : IO Nat := do
  let mut acc := 0
  for _ in *...iters do
    acc := acc + (← IO.getRandomBytes 8).size
  return acc

/-- One server-shaped poll that resolves with the next value of `data`. -/
def poll (ctx : CancellationContext) (data response : Std.Channel Nat) : Async Nat := do
  Selectable.one #[
    .case ctx.doneSelector (fun _ => pure 0),
    .case data.recvSelector pure,
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
    acc := acc + (← poll ctx data response)
  return acc

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
      discard <| requests.send (i + 1)
      acc := acc + (← poll ctx replies idle)
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
  let pings := iters / 10 + 1
  run "poll_pingpong" (pings * (pings + 1) / 2) (benchPollPingPong pings)
