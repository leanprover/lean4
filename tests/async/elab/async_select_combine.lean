import Std.Async
import Std.Sync.Channel

open Std.Async
open Std (CloseableChannel)

def testLateFire : IO (Option Nat) := do
  let ch ← CloseableChannel.new (α := Nat)
  discard <| IO.asTask (prio := .dedicated) do
    IO.sleep 50
    ch.send 1
  let sel ← Selectable.combine #[.case ch.recvSelector fun n? => return n?]
  Async.block do
    Selectable.one #[.case sel fun n? => return n?]

/-- info: some 1 -/
#guard_msgs in
#eval testLateFire

def testReady : IO (Option Nat) := do
  let ch ← CloseableChannel.new (α := Nat)
  ch.sync.send 1
  let sel ← Selectable.combine #[.case ch.recvSelector fun n? => return n?]
  Async.block do
    Selectable.one #[.case sel fun n? => return n?]

/-- info: some 1 -/
#guard_msgs in
#eval testReady
