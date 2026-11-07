import Std.Async.Select
import Std.Sync.Channel

open Std Async

/-!
Tests for the `gate` in `Selectable.one`.
-/
private def immediateSelector (value : α) : Selector α where
  tryFn := pure none
  registerFn waiter := waiter.race (lose := pure ()) (win := fun p => p.resolve (.ok value))
  unregisterFn := pure ()

private def trackingSelector (unregCount : IO.Ref Nat) : Selector Unit where
  tryFn := pure none
  registerFn _ := pure ()
  unregisterFn := unregCount.modify (· + 1)

def testImmediateWins : Async Bool := do
  let cnt ← IO.mkRef 0
  let result ← Selectable.one #[
    .case (immediateSelector 42) pure,
    .case (trackingSelector cnt) fun _ => pure 0,
  ]
  return result == 42 && (← cnt.get) == 1

/-- info: true -/
#guard_msgs in
#eval testImmediateWins.block

def testImmediateWinsAfter : Async Bool := do
  let cnt ← IO.mkRef 0
  let result ← Selectable.one #[
    .case (trackingSelector cnt) fun _ => pure 0,
    .case (immediateSelector 99) pure,
  ]
  return result == 99 && (← cnt.get) == 1

/-- info: true -/
#guard_msgs in
#eval testImmediateWinsAfter.block

-- Both selectors' unregisterFns are called across 500 iterations.
def testUnregisterCalledOnEveryIteration : Async Bool := do
  let mut ok := true
  for i in List.range 500 do
    let cnt ← IO.mkRef 0
    let result ← Selectable.one #[
      .case (immediateSelector i) pure,
      .case (trackingSelector cnt) fun _ => pure 0,
    ]
    if result != i || (← cnt.get) != 1 then ok := false
  return ok

/-- info: true -/
#guard_msgs in
#eval testUnregisterCalledOnEveryIteration.block

-- When there are N tracking selectors, each is unregistered exactly once.
def testAllTrackersUnregistered : Async Bool := do
  let n := 5
  let counters ← (List.range n).mapM fun _ => IO.mkRef 0
  let trackers := counters.map (fun cnt => Selectable.case (trackingSelector cnt) fun _ => pure 0)
  let _ ← Selectable.one (trackers.toArray ++ #[.case (immediateSelector 99) pure])
  let counts ← counters.mapM fun c => c.get
  return counts.all (· == 1)

/-- info: true -/
#guard_msgs in
#eval testAllTrackersUnregistered.block

-- After repeated wins, the channel selector can still deliver messages correctly.
def testChannelUsableAfterRepeatedImmediateWin : Async Bool := do
  let ch : Std.Channel Nat ← Std.Channel.new none
  let cnt ← IO.mkRef 0
  let mut ok := true
  for i in List.range 500 do
    cnt.set 0
    let result ← Selectable.one #[
      .case (immediateSelector i) pure,
      .case ch.recvSelector fun _ => pure 0,
    ]
    if result != i then ok := false
  ch.sync.send 99999
  let last ← Selectable.one #[.case ch.recvSelector pure]
  return ok && last == 99999

/-- info: true -/
#guard_msgs in
#eval testChannelUsableAfterRepeatedImmediateWin.block
