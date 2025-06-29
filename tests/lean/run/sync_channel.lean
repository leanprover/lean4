import Std.Sync

open Std

def assertBEq [BEq α] [ToString α] (is should : α) : IO Unit := do
  if is != should then
    throw <| .userError s!"{is} should be {should}"

def closeClose (ch : CloseableChannel Nat) : IO Unit := do
  assertBEq (← ch.isClosed) false
  assertBEq ((← EIO.toBaseIO ch.close) matches .ok ()) true
  assertBEq (← ch.isClosed) true
  assertBEq ((← EIO.toBaseIO ch.close) matches .error .alreadyClosed) true
  assertBEq (← ch.isClosed) true

def paired (ch : CloseableChannel Nat) : IO Unit := do
  let sendTask ← ch.send 37
  let recvTask ← ch.recv
  assertBEq ((← IO.wait sendTask) matches .ok ()) true
  assertBEq (← IO.wait recvTask) (some 37)

def syncPaired (ch : CloseableChannel.Sync Nat) : IO Unit := do
  let sendTask ← IO.asTask (prio := .dedicated) (EIO.toBaseIO (ch.send 37))
  let recvTask ← IO.asTask (prio := .dedicated) (ch.recv)
  assertBEq ((← IO.ofExcept (← IO.wait sendTask)) matches .ok ()) true
  assertBEq (← IO.ofExcept (← IO.wait recvTask)) (some 37)

def trySend (ch : CloseableChannel Nat) (capacity : Option Nat) : IO Unit := do
  -- ready a receiver ahead of time
  let recvTask ← ch.recv
  assertBEq (← ch.trySend 37) true
  assertBEq (← IO.wait recvTask) (some 37)

  -- the unbounded CloseableChannel cannot go out of space so it is pointless to fill it up
  let some capacity := capacity | return ()
  for i in [:capacity] do
    assertBEq (← ch.trySend i) true

  assertBEq (← ch.trySend (capacity + 1)) false

def tryRecv (ch : CloseableChannel Nat) : IO Unit := do
  assertBEq (← ch.tryRecv) none
  let sendTask ← ch.send 37
  assertBEq (← ch.tryRecv) (some 37)
  assertBEq ((← IO.wait sendTask) matches .ok ()) true

def sendRecvClose (ch : CloseableChannel Nat) : IO Unit := do
  let sendTask ← ch.send 37
  assertBEq ((← EIO.toBaseIO ch.close) matches .ok ()) true
  let recvTask ← ch.recv
  assertBEq ((← IO.wait sendTask) matches .ok ()) true
  assertBEq (← IO.wait recvTask) (some 37)

  let sendTask ← ch.send 37
  assertBEq ((← IO.wait sendTask) matches .error .closed) true
  let recvTask ← ch.recv
  assertBEq (← IO.wait recvTask) none
  assertBEq (← ch.trySend 37) false
  assertBEq (← ch.tryRecv) none

def sendIt (ch : CloseableChannel Nat) (messages : List Nat) : BaseIO (Task (Option Unit)) := do
  match messages with
  | [] => return .pure <| some ()
  | msg :: messages =>
    BaseIO.bindTask (← ch.send msg) fun
      | .error .. =>
        return .pure <| none
      | .ok .. =>
        sendIt ch messages

partial def recvIt (ch : CloseableChannel Nat) (messages : List Nat) : BaseIO (Task (List Nat)) := do
  BaseIO.bindTask (← ch.recv) fun
    | none => return .pure messages.reverse
    | some msg => recvIt ch (msg :: messages)

def sendLots (ch : CloseableChannel Nat) : IO Unit := do
  let messages := List.range 1000
  let sendTask ← sendIt ch messages
  let recvTask ← recvIt ch []
  assertBEq (← IO.wait sendTask) (some ())
  discard <| ch.close
  assertBEq (← IO.wait recvTask) messages

def sendItSync (ch : CloseableChannel.Sync Nat) (messages : List Nat) : IO Unit := do
  for msg in messages do
    ch.send msg
  return ()

def recvItSync (ch : CloseableChannel.Sync Nat) : IO (List Nat) := do
  let mut messages := []
  for msg in ch do
    messages := msg :: messages
  return messages.reverse

def sendLotsSync (ch : CloseableChannel.Sync Nat) : IO Unit := do
  let messages := List.range 1000
  let sendTask ← IO.asTask (prio := .dedicated) (sendItSync ch messages)
  let recvTask ← IO.asTask (prio := .dedicated) (recvItSync ch)
  IO.ofExcept (← IO.wait sendTask)
  discard <| ch.close
  assertBEq (← IO.ofExcept (← IO.wait recvTask)) messages

partial def sendLotsMulti (ch : CloseableChannel Nat) : IO Unit := do
  let messages := List.range 1000
  let sendTask1 ← sendIt ch messages
  let sendTask2 ← sendIt ch messages
  let recvTask1 ← recvIt ch []
  let recvTask2 ← recvIt ch []
  assertBEq (← IO.wait sendTask1) (some ())
  assertBEq (← IO.wait sendTask2) (some ())
  discard <| ch.close
  let msg1 ← IO.wait recvTask1
  let msg2 ← IO.wait recvTask2
  assertBEq (msg1.sum + msg2.sum) (2 * messages.sum)

partial def sendLotsMultiSync (ch : CloseableChannel.Sync Nat) : IO Unit := do
  let messages := List.range 1000
  let sendTask1 ← IO.asTask (prio := .dedicated) (sendItSync ch messages)
  let sendTask2 ← IO.asTask (prio := .dedicated) (sendItSync ch messages)
  let recvTask1 ← IO.asTask (prio := .dedicated) (recvItSync ch)
  let recvTask2 ← IO.asTask (prio := .dedicated) (recvItSync ch)
  IO.ofExcept (← IO.wait sendTask1)
  IO.ofExcept (← IO.wait sendTask2)
  discard <| ch.close
  let msg1 ← IO.ofExcept (← IO.wait recvTask1)
  let msg2 ← IO.ofExcept (← IO.wait recvTask2)
  assertBEq (msg1.sum + msg2.sum) (2 * messages.sum)

def testIt (capacity : Option Nat) : IO Unit := do
  paired (← CloseableChannel.new capacity)
  syncPaired (← CloseableChannel.new capacity).sync

  closeClose (← CloseableChannel.new capacity)
  trySend (← CloseableChannel.new capacity) capacity
  tryRecv (← CloseableChannel.new capacity)
  sendRecvClose (← CloseableChannel.new capacity)

  sendLots (← CloseableChannel.new capacity)
  sendLotsSync (← CloseableChannel.new capacity).sync
  sendLotsMulti (← CloseableChannel.new capacity)
  sendLotsMultiSync (← CloseableChannel.new capacity).sync

def suite : IO Unit := do
  testIt none
  testIt (some 0)
  testIt (some 1)
  testIt (some 8)
  testIt (some 128)

#eval suite
