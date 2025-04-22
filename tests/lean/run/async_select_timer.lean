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

def test2Helper (dur : Time.Millisecond.Offset) : IO (AsyncTask Nat) := do
  Selectable.one #[
    .case (← Selector.sleep dur) fun _ => return AsyncTask.pure 1,
    .case (← Selector.sleep dur) fun _ => return AsyncTask.pure 2,
    .case (← Selector.sleep dur) fun _ => return AsyncTask.pure 3,
    .case (← Selector.sleep dur) fun _ => return AsyncTask.pure 4,
    .case (← Selector.sleep dur) fun _ => return AsyncTask.pure 5,
    .case (← Selector.sleep dur) fun _ => return AsyncTask.pure 6,
    .case (← Selector.sleep dur) fun _ => return AsyncTask.pure 7,
    .case (← Selector.sleep dur) fun _ => return AsyncTask.pure 8,
    .case (← Selector.sleep dur) fun _ => return AsyncTask.pure 9,
    .case (← Selector.sleep dur) fun _ => return AsyncTask.pure 10,
  ]

def test2 (dur : Time.Millisecond.Offset) : IO Bool := do
  let r1 ← IO.ofExcept (← test2Helper dur).get
  let r2 ← IO.ofExcept (← test2Helper dur).get
  let r3 ← IO.ofExcept (← test2Helper dur).get
  let r4 ← IO.ofExcept (← test2Helper dur).get
  let r5 ← IO.ofExcept (← test2Helper dur).get
  let r6 ← IO.ofExcept (← test2Helper dur).get
  let r7 ← IO.ofExcept (← test2Helper dur).get
  let r8 ← IO.ofExcept (← test2Helper dur).get
  let r9 ← IO.ofExcept (← test2Helper dur).get
  let r10 ← IO.ofExcept (← test2Helper dur).get
  return #[r2, r3, r4, r5, r6, r7, r8, r9, r10].any (· != r1)

/-- info: true -/
#guard_msgs in
#eval test2 100

/-- info: true -/
#guard_msgs in
#eval test2 0
