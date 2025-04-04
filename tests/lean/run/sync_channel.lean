import Std.Sync.NewChannel

open Std.Experimental

def assertBEq [BEq α] [ToString α] (is should : α) : IO Unit := do
  if is != should then
    throw <| .userError s!"{is} should be {should}"

def paired (ch : Channel Nat) : IO Unit := do
  let sendTask ← ch.send 37
  let recvTask ← ch.recv
  assertBEq (← IO.wait sendTask) (some ())
  assertBEq (← IO.wait recvTask) (some 37)

def syncPaired (ch : Channel.Sync Nat) : IO Unit := do
  let sendTask ← IO.asTask (prio := .dedicated) (ch.send 37)
  let recvTask ← IO.asTask (prio := .dedicated) (ch.recv)
  assertBEq (← IO.ofExcept (← IO.wait sendTask)) (some ())
  assertBEq (← IO.ofExcept (← IO.wait recvTask)) (some 37)

def sendIt (ch : Channel Nat) (messages : List Nat) : BaseIO (Task (Option Unit)) := do
  match messages with
  | [] => return .pure <| some ()
  | msg :: messages =>
    BaseIO.bindTask (← ch.send msg) fun
      | none =>
        return .pure <| none
      | some _ =>
        sendIt ch messages

partial def recvIt (ch : Channel Nat) (messages : List Nat) : BaseIO (Task (List Nat)) := do
  BaseIO.bindTask (← ch.recv) fun
    | none => return .pure messages.reverse
    | some msg => recvIt ch (msg :: messages)

def sendLots (ch : Channel Nat) : IO Unit := do
  let messages := List.range 1000
  let sendTask ← sendIt ch messages
  let recvTask ← recvIt ch []
  assertBEq (← IO.wait sendTask) (some ())
  ch.close
  assertBEq (← IO.wait recvTask) messages

def sendItSync (ch : Channel.Sync Nat) (messages : List Nat) : IO (Option Unit) := do
  for msg in messages do
    if let none ← ch.send msg then
      return none
  return some ()

def recvItSync (ch : Channel.Sync Nat) : IO (List Nat) := do
  let mut messages := []
  for msg in ch do
    messages := msg :: messages
  return messages.reverse

def sendLotsSync (ch : Channel.Sync Nat) : IO Unit := do
  let messages := List.range 1000
  let sendTask ← IO.asTask (prio := .dedicated) (sendItSync ch messages)
  let recvTask ← IO.asTask (prio := .dedicated) (recvItSync ch)
  assertBEq (← IO.ofExcept (← IO.wait sendTask)) (some ())
  ch.close
  assertBEq (← IO.ofExcept (← IO.wait recvTask)) messages

partial def sendLotsMulti (ch : Channel Nat) : IO Unit := do
  let messages := List.range 1000
  let sendTask1 ← sendIt ch messages
  let sendTask2 ← sendIt ch messages
  let recvTask1 ← recvIt ch []
  let recvTask2 ← recvIt ch []
  assertBEq (← IO.wait sendTask1) (some ())
  assertBEq (← IO.wait sendTask2) (some ())
  ch.close
  let msg1 ← IO.wait recvTask1
  let msg2 ← IO.wait recvTask2
  assertBEq (msg1.sum + msg2.sum) (2 * messages.sum)

partial def sendLotsMultiSync (ch : Channel.Sync Nat) : IO Unit := do
  let messages := List.range 1000
  let sendTask1 ← IO.asTask (prio := .dedicated) (sendItSync ch messages)
  let sendTask2 ← IO.asTask (prio := .dedicated) (sendItSync ch messages)
  let recvTask1 ← IO.asTask (prio := .dedicated) (recvItSync ch)
  let recvTask2 ← IO.asTask (prio := .dedicated) (recvItSync ch)
  assertBEq (← IO.ofExcept (← IO.wait sendTask1)) (some ())
  assertBEq (← IO.ofExcept (← IO.wait sendTask2)) (some ())
  ch.close
  let msg1 ← IO.ofExcept (← IO.wait recvTask1)
  let msg2 ← IO.ofExcept (← IO.wait recvTask2)
  assertBEq (msg1.sum + msg2.sum) (2 * messages.sum)

def testIt (mkChannel : BaseIO (Channel Nat)) : IO Unit := do
  paired (← mkChannel)
  sendLots (← mkChannel)
  sendLotsMulti (← mkChannel)

  syncPaired (← mkChannel).sync
  sendLotsSync (← mkChannel).sync
  sendLotsMultiSync (← mkChannel).sync

def suite : IO Unit := do
  testIt (Channel.new none)
  testIt (Channel.new (some 0))
  testIt (Channel.new (some 1))
  -- TODO: broken
  -- testIt (Channel.new (some 8))

#eval! suite
