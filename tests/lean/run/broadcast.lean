import Std.Internal.Async
import Std.Sync

open Std.Internal.IO Async

-- Test tryRecv with empty channel
def tryRecvEmpty : Async Unit := do
  let channel ← Std.Broadcast.new (capacity := 4) (α := Nat)
  let subs ← channel.subscribe

  let result ← subs.tryRecv
  assert! result.isNone

#eval tryRecvEmpty.block

-- Test tryRecv with messages available
def tryRecvWithMessages : Async Unit := do
  let channel ← Std.Broadcast.new (capacity := 4)
  let subs ← channel.subscribe

  discard <| await (← channel.send 42)
  discard <| await (← channel.send 100)

  let msg1 ← subs.tryRecv
  let msg2 ← subs.tryRecv
  let msg3 ← subs.tryRecv

  assert! msg1 == some 42
  assert! msg2 == some 100
  assert! msg3.isNone

#eval tryRecvWithMessages.block

-- Test unsubscribe functionality
def testUnsubscribe : Async Unit := do
  let channel ← Std.Broadcast.new (capacity := 4)
  let subs1 ← channel.subscribe
  let subs2 ← channel.subscribe

  -- Send before unsubscribe
  discard <| await (← channel.send 1)

  -- Unsubscribe subs1
  subs1.unsubscribe

  -- Send after unsubscribe
  discard <| await (← channel.send 2)

  -- subs1 should not receive the second message
  let msg1 ← await (← subs1.recv)
  let result ← subs1.tryRecv

  -- subs2 should receive both messages
  let msg2 ← await (← subs2.recv)
  let msg3 ← await (← subs2.recv)

  assert! msg1 == none
  assert! result.isNone  -- No more messages for unsubscribed
  assert! msg2 == some 1
  assert! msg3 == some 2

#eval testUnsubscribe.block

def testUnsubscribeUnblock : Async Unit := do
  let channel ← Std.Broadcast.new (capacity := 4)

  let subs1 ← channel.subscribe
  let subs2 ← channel.subscribe

  -- Add 4 messages, so it reaches the limit.
  for i in [0:4] do
    assert! (← channel.trySend i)

  -- Mark subs1 messages as read
  for i in [0:10] do
    if i < 4 then
      assert! (← subs1.tryRecv) = some i
    else
      assert! (← subs1.tryRecv) = none

  -- Mark 2 messages as read so it cleans 2 messages
  assert! (← subs2.tryRecv).isSome
  assert! (← subs2.tryRecv).isSome

  assert! (← channel.trySend 5)
  assert! (← channel.trySend 5)
  assert! not (← channel.trySend 6)

  -- It unsubscribe and mark all subs2 messages as read.
  subs2.unsubscribe

  -- Create a new subscriber to verify channel still works
  let subs3 ← channel.subscribe

  -- Send one more message that the new subscriber should receive
  assert! (← channel.trySend 8)

  -- subs1 should be able to receive the messages sent after it last read:
  -- the two 5's and the 8
  let subs1Msg1 ← subs1.tryRecv
  let subs1Msg2 ← subs1.tryRecv
  let subs1Msg3 ← subs1.tryRecv
  let subs1Msg4 ← subs1.tryRecv -- should be none

  assert! subs1Msg1 == some 5
  assert! subs1Msg2 == some 5
  assert! subs1Msg3 == some 8
  assert! subs1Msg4.isNone

  -- The new subscriber should only get the most recent message
  let msg ← subs3.tryRecv
  assert! msg == some 8

  -- No more messages should be available for the new subscriber
  let noMsg ← subs3.tryRecv
  assert! noMsg.isNone

  -- Verify unsubscribed subs2 can't receive anything
  let subs2NoMsg ← subs2.tryRecv
  assert! subs2NoMsg.isNone

#eval testUnsubscribeUnblock.block

def unsubscribedCannotReceive : Async Unit := do
  let channel ← Std.Broadcast.new

  let subs1 ← channel.subscribe
  let subs2 ← channel.subscribe

  discard <| await (← channel.send 1)
  discard <| await (← channel.send 2)

  let msg1 ← await (← subs1.recv)
  let msg2 ← await (← subs1.recv)
  let msg3 ← await (← subs2.recv)
  let msg4 ← await (← subs2.recv)

  assert! msg1 == some 1
  assert! msg2 == some 2

  assert! msg3 == some 1
  assert! msg4 == some 2

#eval unsubscribedCannotReceive.block

def fullBuffer : Async Unit := do
  let channel ← Std.Broadcast.new (capacity := 4)

  let subs1 ← channel.subscribe

  for i in [0:5] do
    if not (← channel.trySend i) then
      assert! i == 4

#eval fullBuffer.block

def noSubscribers : Async Unit := do
  let channel ← Std.Broadcast.new (capacity := 4)

  assert! not (← channel.trySend 0)

#eval noSubscribers.block

-- Test unsubscribe during message consumption
def testUnsubscribeDuringConsumption : Async Unit := do
  let channel ← Std.Broadcast.new (capacity := 4)
  let subs1 ← channel.subscribe
  let subs2 ← channel.subscribe

  -- Send several messages
  for i in [0:4] do
    discard <| await (← channel.send i)

  -- subs1 reads first message then unsubscribes
  let msg1 ← await (← subs1.recv)
  subs1.unsubscribe

  -- subs2 should still be able to read all messages
  let msgs2 ← [0, 1, 2, 3].mapM (fun _ => subs2.recv >>= fun r => await r)

  assert! msg1 == some 0
  assert! msgs2 == [some 0, some 1, some 2, some 3]

  -- subs1 should have no more messages available
  let result ← subs1.tryRecv
  assert! result.isNone

-- Test mixed send and trySend operations
def testMixedSendOperations : Async Unit := do
  let channel ← Std.Broadcast.new (capacity := 3)
  let subs ← channel.subscribe

  -- Use trySend
  assert! (← channel.trySend 1)

  -- Use regular send
  discard <| await (← channel.send 2)

  -- Use trySend again
  assert! (← channel.trySend 3)

  -- Buffer should be full now
  assert! not (← channel.trySend 4)

  -- Verify all messages received correctly
  let msgs ← [1, 2, 3].mapM (fun _ => subs.recv >>= fun r => await r)
  assert! msgs == [some 1, some 2, some 3]

#eval testMixedSendOperations.block

-- Test recv on closed channel with no pending messages
def testRecvOnClosedEmpty : Async Unit := do
  let channel ← Std.Broadcast.new (capacity := 4) (α := Nat)
  let subs ← channel.subscribe

  channel.close

  -- tryRecv should return none immediately
  let result ← subs.tryRecv
  assert! result.isNone

#eval testRecvOnClosedEmpty.block
