import Std.Internal.Async
import Std.Sync

open Std.Internal.IO Async

-- Test basic cancellation with default reason
def testBasicCancellationWithReason : Async Unit := do
  let token ← Std.CancellationToken.new
  assert! not (← token.isCancelled)

  token.cancel
  assert! (← token.isCancelled)

  let reason ← token.getCancellationReason
  assert! reason == some .cancel

#eval testBasicCancellationWithReason.block

-- Test cancellation with deadline reason
def testDeadlineReason : Async Unit := do
  let token ← Std.CancellationToken.new
  assert! not (← token.isCancelled)

  token.cancel .deadline
  assert! (← token.isCancelled)

  let reason ← token.getCancellationReason
  assert! reason == some .deadline

#eval testDeadlineReason.block

-- Test cancellation with shutdown reason
def testShutdownReason : Async Unit := do
  let token ← Std.CancellationToken.new
  token.cancel .shutdown

  let reason ← token.getCancellationReason
  assert! reason == some .shutdown

#eval testShutdownReason.block

-- Test cancellation with custom reason
def testCustomReason : Async Unit := do
  let token ← Std.CancellationToken.new
  token.cancel (.custom "connection timeout")

  let reason ← token.getCancellationReason
  assert! reason == some (.custom "connection timeout")

#eval testCustomReason.block

-- Test that uncancelled token has no reason
def testUncancelledNoReason : Async Unit := do
  let token ← Std.CancellationToken.new

  let reason ← token.getCancellationReason
  assert! reason == none

#eval testUncancelledNoReason.block

-- Test context cancellation with reason
def testContextCancellation : Async Unit := do
  let ctx ← Std.CancellationContext.new
  assert! not (← ctx.isCancelled)

  ctx.cancel .shutdown
  assert! (← ctx.isCancelled)

  let reason ← ctx.token.getCancellationReason
  assert! reason == some .shutdown

#eval testContextCancellation.block

-- Test context tree with different reasons
def testContextTreeReasons : Async Unit := do
  let root ← Std.CancellationContext.new
  let child1 ← root.fork
  let child2 ← root.fork
  let grandchild ← child1.fork

  -- Cancel root with shutdown reason
  root.cancel .shutdown

  -- All should be cancelled
  assert! (← root.isCancelled)
  assert! (← child1.isCancelled)
  assert! (← child2.isCancelled)
  assert! (← grandchild.isCancelled)

  -- All should have the shutdown reason (propagated from root)
  assert! (← root.token.getCancellationReason) == some .shutdown
  assert! (← child1.token.getCancellationReason) == some .shutdown
  assert! (← child2.token.getCancellationReason) == some .shutdown
  assert! (← grandchild.token.getCancellationReason) == some .shutdown

#eval testContextTreeReasons.block

-- Test child cancellation doesn't affect parent
def testChildCancellationIndependent : Async Unit := do
  let root ← Std.CancellationContext.new
  let child ← root.fork

  -- Cancel child with deadline
  child.cancel .deadline

  -- Child should be cancelled with deadline reason
  assert! (← child.isCancelled)
  assert! (← child.token.getCancellationReason) == some .deadline

  -- Parent should still be active
  assert! not (← root.isCancelled)
  assert! (← root.token.getCancellationReason) == none

#eval testChildCancellationIndependent.block

-- Test selector with reason
def testSelectorWithReason : Async Unit := do
  let token ← Std.CancellationToken.new
  let completed ← Std.Mutex.new false
  let reasonRef ← Std.Mutex.new none

  let task ← async do
    Selectable.one #[.case token.selector (fun _ => pure ())]
    completed.atomically (set true)
    reasonRef.atomically (set (← token.getCancellationReason))

  assert! not (← completed.atomically get)

  token.cancel .deadline
  await task

  assert! (← completed.atomically get)
  assert! (← reasonRef.atomically get) == some Std.CancellationReason.deadline

#eval testSelectorWithReason.block

-- Test wait with reason
def testWaitWithReason : Async Unit := do
  let token ← Std.CancellationToken.new

  let task ← async do
    let _ ← await (← token.wait)
    token.getCancellationReason

  Async.sleep 10
  token.cancel (.custom "test reason")

  let reason ← await task
  assert! reason == some (.custom "test reason")

#eval testWaitWithReason.block

-- Test multiple cancellations (first one wins)
def testMultipleCancellations : Async Unit := do
  let token ← Std.CancellationToken.new

  token.cancel .deadline
  token.cancel .shutdown -- This should be ignored

  let reason ← token.getCancellationReason
  assert! reason == some .deadline -- First reason should persist

#eval testMultipleCancellations.block
