import Std.Sync.Channel


/-
Inspired by:
https://github.com/crossbeam-rs/crossbeam/tree/bd87a61ce3858ca772c42525d5f0c9aa12cc80ac/crossbeam-channel/benchmarks.

We conduct for:
- capacity 0 channels
- capacity 1 channels
- capacity `N` channels
- unbounded channels

the following tests:
- `seq`: A single thread sends `N` messages. Then it receives `N` messages.
- `spsc`: One thread sends `N` messages. Another thread receives `N` messages.
- `mpsc`: `T` threads send `N / T` messages each. One thread receives `N` messages.
- `mpmc`: `T` threads send `N / T` messages each. `T` other threads receive `N / T` messages each.

Note that we will stick exclusively to the sync interface for this as there is no benefit to be
reaped from async in this benchmark so we might as well just block.
-/

def MESSAGES : Nat := 1_000_000
def THREADS : Nat := 4

def seq (ch : Std.CloseableChannel.Sync Nat) (amount : Nat) : IO Unit := do
  for i in [:amount] do
    ch.send i

  for _ in [:amount] do
    discard <| ch.recv

def spsc (ch : Std.CloseableChannel.Sync Nat) (amount : Nat) : IO Unit := do
  let t1 ← IO.asTask (prio := .dedicated) do
    for i in [:amount] do
      ch.send i

  let t2 ← BaseIO.asTask (prio := .dedicated) do
    for _ in [:amount] do
      discard <| ch.recv

  IO.ofExcept (← IO.wait t1)
  IO.wait t2

def mpsc (ch : Std.CloseableChannel.Sync Nat) (amount : Nat) : IO Unit := do
  let mut producers := Array.emptyWithCapacity THREADS
  for _ in [:THREADS] do
    let t ← IO.asTask (prio := .dedicated) do
      for i in [:(amount/THREADS)] do
        ch.send i
    producers := producers.push t

  let consumer ← BaseIO.asTask (prio := .dedicated) do
    for _ in [:amount] do
      discard <| ch.recv

  IO.wait consumer
  for producer in producers do
    (IO.ofExcept (← IO.wait producer))

def mpmc (ch : Std.CloseableChannel.Sync Nat) (amount : Nat) : IO Unit := do
  let mut producers := Array.emptyWithCapacity THREADS
  for _ in [:THREADS] do
    let t ← IO.asTask (prio := .dedicated) do
      for i in [:(amount/THREADS)] do
        ch.send i
    producers := producers.push t

  let mut consumers := Array.emptyWithCapacity THREADS
  for _ in [:THREADS] do
    let t ← IO.asTask (prio := .dedicated) do
      while true do
        if let some _ ← ch.recv then
          continue
        else
          break
    consumers := consumers.push t

  for producer in producers do
    (IO.ofExcept (← IO.wait producer))

  ch.close

  for consumer in consumers do
    (IO.ofExcept (← IO.wait consumer))

  return ()

def run (name : String) (cap : Option Nat) (bench : Std.CloseableChannel.Sync Nat → Nat → IO Unit) :
    IO Unit := do
  let ch ← Std.CloseableChannel.new cap
  let t1 ← IO.monoMsNow
  bench ch.sync MESSAGES
  let t2 ← IO.monoMsNow
  let time : Float := (t2 - t1).toFloat / 1000.0
  IO.println s!"{name}: {time}"


def main : IO Unit := do
  run "bounded0_spsc" (some 0) spsc
  run "bounded0_mpsc" (some 0) mpsc
  run "bounded0_mpmc" (some 0) mpmc

  run "bounded1_spsc" (some 1) spsc
  run "bounded1_mpsc" (some 1) mpsc
  run "bounded1_mpmc" (some 1) mpmc

  run "boundedn_spsc" (some MESSAGES) spsc
  run "boundedn_mpsc" (some MESSAGES) mpsc
  run "boundedn_mpmc" (some MESSAGES) mpmc
  run "boundedn_seq" (some MESSAGES) seq

  run "unbounded_spsc" none spsc
  run "unbounded_mpsc" none mpsc
  run "unbounded_mpmc" none mpmc
  run "unbounded_seq" none seq
