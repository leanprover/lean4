import Std.Sync.Channel

open Std Internal IO Async

namespace A

def testReceiver (ch1 ch2 : Std.Channel Nat) (count : Nat) : Async Nat := do
  go ch1 ch2 count 0
where
  go (ch1 ch2 : Std.Channel Nat) (count : Nat) (acc : Nat) : Async Nat := do
    match count with
    | 0 => return acc
    | count + 1 =>
      Selectable.one #[
        .case ch1.recvSelector fun data => go ch1 ch2 count (acc + data),
        .case ch2.recvSelector fun data => go ch1 ch2 count (acc + data),
      ]

def testIt (capacity : Option Nat) : Async Bool := do
  let amount := 1000
  let messages := Array.range amount
  let ch1 ← Std.Channel.new capacity
  let ch2 ← Std.Channel.new capacity
  let recvTask ← async (testReceiver ch1 ch2 amount)

  for msg in messages do
    if (← IO.rand 0 1) = 0 then
      ch1.sync.send msg
    else
      ch2.sync.send msg

  let acc ← await recvTask
  return acc == messages.sum

/-- info: true -/
#guard_msgs in
#eval testIt none |>.block

/-- info: true -/
#guard_msgs in
#eval testIt (some 0) |>.block

/-- info: true -/
#guard_msgs in
#eval testIt (some 1) |>.block

/-- info: true -/
#guard_msgs in
#eval testIt (some 128) |>.block

end A

namespace B

def testReceiver (ch1 ch2 : Std.CloseableChannel Nat) (count : Nat) : Async Nat := do
  go ch1 ch2 count 0
where
  go (ch1 ch2 : Std.CloseableChannel Nat) (count : Nat) (acc : Nat) : Async Nat := do
    match count with
    | 0 => return acc
    | count + 1 =>
      Selectable.one #[
        .case ch1.recvSelector fun data => go ch1 ch2 count (acc + data.getD 0),
        .case ch2.recvSelector fun data => go ch1 ch2 count (acc + data.getD 0),
      ]

def testIt (capacity : Option Nat) : Async Bool := do
  let amount := 1000
  let messages := Array.range amount
  let ch1 ← Std.CloseableChannel.new capacity
  let ch2 ← Std.CloseableChannel.new capacity
  let recvTask ← async (testReceiver ch1 ch2 amount)

  for msg in messages do
    if (← IO.rand 0 1) = 0 then
      ch1.sync.send msg
    else
      ch2.sync.send msg

  let acc ← await recvTask
  -- TODO: we seem to nondeterministically create reference cycles without these, investigate
  ch1.close
  ch2.close
  return acc == messages.sum

/-- info: true -/
#guard_msgs in
#eval testIt none |>.block

/-- info: true -/
#guard_msgs in
#eval testIt (some 0) |>.block

/-- info: true -/
#guard_msgs in
#eval testIt (some 1) |>.block

/-- info: true -/
#guard_msgs in
#eval testIt (some 128) |>.block

end B
