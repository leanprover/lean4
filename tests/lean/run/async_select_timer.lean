import Std.Internal.Async.Timer

open Std Internal IO Async

def test1 : IO (AsyncTask Nat) := do
  let s1 ← Sleep.mk 1000
  let s2 ← Sleep.mk 1500
  Selectable.one #[
    .case (← s2.selector) fun _ => return AsyncTask.pure 2,
    .case (← s1.selector) fun _ => return AsyncTask.pure 1,
  ]

/-- info: 1 -/
#guard_msgs in
#eval show IO _ from do
  let task ← test1
  IO.ofExcept task.get

def test2 : IO (AsyncTask Nat) := do
  Selectable.one #[
    .case (← Selector.sleep 1500) fun _ => return AsyncTask.pure 2,
    .case (← Selector.sleep 1000) fun _ => return AsyncTask.pure 1,
  ]

/-- info: 1 -/
#guard_msgs in
#eval show IO _ from do
  let task ← test2
  IO.ofExcept task.get
