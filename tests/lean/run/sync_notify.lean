import Std.Internal.Async
import Std.Sync

open Std.Internal.IO Async

-- Test basic wait and notifyOne functionality
def testBasicWaitNotifyOne : Async Unit := do
  let notify ← Std.Notify.new
  let waitTask ← notify.wait

  assert! (← waitTask.getState) = .waiting
  discard <| notify.notifyOne
  await waitTask
  assert! (← waitTask.getState) = .finished

#eval testBasicWaitNotifyOne.block

-- Test multiple waiters with notifyOne (only one should be notified)
def testMultipleWaitersNotifyOne : Async Unit := do
  let notify ← Std.Notify.new
  let task1 ← notify.wait
  let task2 ← notify.wait
  let task3 ← notify.wait

  assert! (← task1.getState) = .waiting
  assert! (← task2.getState) = .waiting
  assert! (← task3.getState) = .waiting

  discard <| notify.notifyOne

  IO.sleep 100

  let states ← [task1, task2, task3].mapM (fun t => t.getState)
  let finishedCount := states.filter (· == .finished) |>.length
  let waitingCount := states.filter (· == .waiting) |>.length

  assert! finishedCount == 1
  assert! waitingCount == 2

  discard <| notify.notifyOne

#eval testMultipleWaitersNotifyOne.block

-- Test multiple waiters with notify (all should be notified)
def testMultipleWaitersNotifyAll : Async Unit := do
  let notify ← Std.Notify.new
  let task1 ← notify.wait
  let task2 ← notify.wait
  let task3 ← notify.wait

  assert! (← task1.getState) = .waiting
  assert! (← task2.getState) = .waiting
  assert! (← task3.getState) = .waiting

  discard <| notify.notify

  await task1
  await task2
  await task3

  assert! (← task1.getState) = .finished
  assert! (← task2.getState) = .finished
  assert! (← task3.getState) = .finished

#eval testMultipleWaitersNotifyAll.block

-- Test sequential notification
def testSequentialNotification : Async Unit := do
  let notify ← Std.Notify.new
  let task1 ← notify.wait
  let task2 ← notify.wait
  let task3 ← notify.wait

  discard <| notify.notifyOne
  await task1
  assert! (← task1.getState) = .finished
  assert! (← task2.getState) = .waiting
  assert! (← task3.getState) = .waiting

  discard <| notify.notifyOne
  await task2
  assert! (← task2.getState) = .finished
  assert! (← task3.getState) = .waiting

  discard <| notify.notifyOne
  await task3
  assert! (← task3.getState) = .finished

#eval testSequentialNotification.block

def testReuseAfterCompletion : Async Unit := do
  let notify ← Std.Notify.new

  let task1 ← notify.wait
  discard <| notify.notifyOne
  await task1
  assert! (← task1.getState) = .finished

  let task2 ← notify.wait
  let task3 ← notify.wait
  discard <| notify.notify
  await task2
  await task3

  assert! (← task2.getState) = .finished
  assert! (← task3.getState) = .finished

#eval testReuseAfterCompletion.block
