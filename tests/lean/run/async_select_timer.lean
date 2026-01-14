import Std.Internal.Async.Timer

open Std Internal IO Async

def test1 : Async Nat := do
  let s1 ← Sleep.mk 1000
  let s2 ← Sleep.mk 1500

  Selectable.one #[
    .case (s2.selector) fun _ => return 2,
    .case (s1.selector) fun _ => return 1,
  ]

/-- info: 1 -/
#guard_msgs in
#eval test1 |>.block

def test2 : Async Nat := do
  Selectable.one #[
    .case (← Selector.sleep 1500) fun _ => return 2,
    .case (← Selector.sleep 1000) fun _ => return 1,
  ]

/-- info: 1 -/
#guard_msgs in
#eval EAsync.block <| show Async _ from do
  test2

/-- error: Selectable.one requires at least one Selectable -/
#guard_msgs in
#eval EAsync.block <| show Async _ from do
  let foo ← Selectable.one (α := Unit) #[]
