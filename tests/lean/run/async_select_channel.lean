import Std.Sync.Channel

open Std Internal IO Async

namespace A

def testReceiver (ch1 ch2 : Std.Channel Nat) (count : Nat) : IO (AsyncTask Nat) := do
  go ch1 ch2 count 0
where
  go (ch1 ch2 : Std.Channel Nat) (count : Nat) (acc : Nat) : IO (AsyncTask Nat) := do
    match count with
    | 0 => return AsyncTask.pure acc
    | count + 1 =>
      Selectable.one #[
        .case ch1.recvSelector fun data => go ch1 ch2 count (acc + data),
        .case ch2.recvSelector fun data => go ch1 ch2 count (acc + data),
      ]

def testIt (capacity : Option Nat) : IO Bool := do
  let amount := 1000
  let messages := Array.range amount
  let ch1 ← Std.Channel.new capacity
  let ch2 ← Std.Channel.new capacity
  let recvTask ← testReceiver ch1 ch2 amount

  for msg in messages do
    if (← IO.rand 0 1) = 0 then
      ch1.sync.send msg
    else
      ch2.sync.send msg

  let acc ← recvTask.block
  return acc == messages.sum

/-- info: true -/
#guard_msgs in
#eval testIt none

/-- info: true -/
#guard_msgs in
#eval testIt (some 0)

/-- info: true -/
#guard_msgs in
#eval testIt (some 1)

/-- info: true -/
#guard_msgs in
#eval testIt (some 128)

end A

namespace B

def testReceiver (ch1 ch2 : Std.CloseableChannel Nat) (count : Nat) : IO (AsyncTask Nat) := do
  go ch1 ch2 count 0
where
  go (ch1 ch2 : Std.CloseableChannel Nat) (count : Nat) (acc : Nat) : IO (AsyncTask Nat) := do
    match count with
    | 0 => return AsyncTask.pure acc
    | count + 1 =>
      Selectable.one #[
        .case ch1.recvSelector fun data => go ch1 ch2 count (acc + data.getD 0),
        .case ch2.recvSelector fun data => go ch1 ch2 count (acc + data.getD 0),
      ]

def testIt (capacity : Option Nat) : IO Bool := do
  let amount := 1000
  let messages := Array.range amount
  let ch1 ← Std.CloseableChannel.new capacity
  let ch2 ← Std.CloseableChannel.new capacity
  let recvTask ← testReceiver ch1 ch2 amount

  for msg in messages do
    if (← IO.rand 0 1) = 0 then
      ch1.sync.send msg
    else
      ch2.sync.send msg

  let acc ← recvTask.block
  return acc == messages.sum

/-- info: true -/
#guard_msgs in
#eval testIt none

/-- info: true -/
#guard_msgs in
#eval testIt (some 0)

/-- info: true -/
#guard_msgs in
#eval testIt (some 1)

/-- info: true -/
#guard_msgs in
#eval testIt (some 128)

end B
