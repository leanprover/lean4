import Std.Internal.Async
import Std.Sync

open Std.Internal.IO Async

/-- Test basic tree cancellation -/
partial def testCancelTree : IO Unit := do
  let mutex ← Std.Mutex.new 0
  let context ← Std.CancellationContext.new

  Async.block do

    let rec loop (x : Nat) (parent : Std.CancellationContext) : Async Unit := do
      match x with
      | 0 => do
          await (← parent.done)
          mutex.atomically (modify (· + 1))

      | n + 1 => do
          background (loop n (← parent.fork))
          background (loop n (← parent.fork))
          await (← parent.done)
          mutex.atomically (modify (· + 1))

    background (loop 3 context)
    Async.sleep 500
    context.cancel .cancel
    Async.sleep 1000

  assert! (← context.countAliveTokens) == 0
  let size ← mutex.atomically get
  IO.println s!"cancelled {size}"

/--
info: cancelled 15
-/
#guard_msgs in
#eval testCancelTree

/-- Test cancellation with different reasons -/
def testCancellationReasons : IO Unit := do
  let ctx ← Std.CancellationContext.new
  let (reason1, reason2, reason3, reason4) ← Async.block do
    -- Test with .cancel reason
    let ctx1 ← ctx.fork
    ctx1.cancel .cancel
    let some reason1 ← ctx1.getCancellationReason | return (none, none, none, none)

    -- Test with .deadline reason
    let ctx2 ← ctx.fork
    ctx2.cancel .deadline
    let some reason2 ← ctx2.getCancellationReason | return (none, none, none, none)

    -- Test with .shutdown reason
    let ctx3 ← ctx.fork
    ctx3.cancel .shutdown
    let some reason3 ← ctx3.getCancellationReason | return (none, none, none, none)

    -- Test with custom reason
    let ctx4 ← ctx.fork
    ctx4.cancel (.custom "test error")
    let some reason4 ← ctx4.getCancellationReason | return (none, none, none, none)

    return (some reason1, some reason2, some reason3, some reason4)

  if let some r1 := reason1 then IO.println s!"Reason 1: {r1}"
  if let some r2 := reason2 then IO.println s!"Reason 2: {r2}"
  if let some r3 := reason3 then IO.println s!"Reason 3: {r3}"
  if let some r4 := reason4 then IO.println s!"Reason 4: {r4}"

  assert! (← ctx.countAliveTokens) == 1

/--
info: Reason 1: cancel
Reason 2: deadline
Reason 3: shutdown
Reason 4: custom("test error")
-/
#guard_msgs in
#eval testCancellationReasons

/-- Test cancellation propagates reason to children -/
def testReasonPropagation : IO Unit := do
  let (parentReason, child1Reason, child2Reason, grandchildReason) ← Async.block do
    let parent ← Std.CancellationContext.new
    let child1 ← parent.fork
    let child2 ← parent.fork
    let grandchild ← child1.fork

    parent.cancel (.custom "parent cancelled")
    Async.sleep 100

    let some parentReason ← parent.getCancellationReason | return (none, none, none, none)
    let some child1Reason ← child1.getCancellationReason | return (none, none, none, none)
    let some child2Reason ← child2.getCancellationReason | return (none, none, none, none)
    let some grandchildReason ← grandchild.getCancellationReason | return (none, none, none, none)

    return (some parentReason, some child1Reason, some child2Reason, some grandchildReason)

  if let some r := parentReason then IO.println s!"Parent: {r}"
  if let some r := child1Reason then IO.println s!"Child1: {r}"
  if let some r := child2Reason then IO.println s!"Child2: {r}"
  if let some r := grandchildReason then IO.println s!"Grandchild: {r}"

/--
info: Parent: custom("parent cancelled")
Child1: custom("parent cancelled")
Child2: custom("parent cancelled")
Grandchild: custom("parent cancelled")
-/
#guard_msgs in
#eval testReasonPropagation

/-- Test cancellation in the middle of work -/
def testCancelInMiddle : IO Unit := do
  let counter ← Std.Mutex.new 0
  let cancelledCounter ← Std.Mutex.new 0

  let (finalCount, cancelledCount) ← Async.block do
    let context ← Std.CancellationContext.new

    -- Worker that does work until cancelled
    let worker (ctx : Std.CancellationContext) : Async Unit := do
      for _ in [0:100] do
        if ← ctx.isCancelled then
          cancelledCounter.atomically (modify (· + 1))
          break
        counter.atomically (modify (· + 1))
        Async.sleep 10

    -- Start 5 workers
    for _ in [0:5] do
      background (worker context)

    -- Let them run for a bit, then cancel
    Async.sleep 200
    context.cancel .deadline

    -- Wait for them to finish
    Async.sleep 500

    let finalCount ← counter.atomically get
    let cancelledCount ← cancelledCounter.atomically get
    return (finalCount, cancelledCount)

  IO.println s!"Completed {finalCount} iterations before cancellation"
  IO.println s!"{cancelledCount} workers detected cancellation"

/-- Test cancellation before forking -/
def testCancelBeforeFork : IO Unit := do
  let (isSame, isChildCancelled) ← Async.block do
    let ctx ← Std.CancellationContext.new
    ctx.cancel .cancel

    -- Fork after cancellation should return same context
    let child ← ctx.fork
    let isSame := ctx.id == child.id
    let isChildCancelled ← child.isCancelled

    return (isSame, isChildCancelled)

  IO.println s!"Same context: {isSame}, Child cancelled: {isChildCancelled}"

/--
info: Same context: true, Child cancelled: true
-/
#guard_msgs in
#eval testCancelBeforeFork

/-- Test deep tree cancellation with reason -/
partial def testDeepTreeCancellation : IO Unit := do
  let depths ← Std.Mutex.new ([] : List (Nat × Std.CancellationReason))

  let (count, allSameReason) ← Async.block do
    let root ← Std.CancellationContext.new

    let rec makeTree (depth : Nat) (ctx : Std.CancellationContext) : Async Unit := do
      if depth == 0 then
        await (← ctx.done)
        if let some reason ← ctx.getCancellationReason then
          depths.atomically (modify (·.cons (depth, reason)))
      else
        let child1 ← ctx.fork
        let child2 ← ctx.fork
        background (makeTree (depth - 1) child1)
        background (makeTree (depth - 1) child2)
        await (← ctx.done)
        if let some reason ← ctx.getCancellationReason then
          depths.atomically (modify (·.cons (depth, reason)))

    background (makeTree 4 root)
    Async.sleep 200
    root.cancel (.custom "deep tree cancel")
    Async.sleep 500

    let results ← depths.atomically get
    let count := results.length
    let allSameReason := results.all fun (_, r) => r == .custom "deep tree cancel"
    return (count, allSameReason)

  IO.println s!"Cancelled {count} nodes, all with same reason: {allSameReason}"

/--
info: Cancelled 31 nodes, all with same reason: true
-/
#guard_msgs in
#eval testDeepTreeCancellation

/-- Test counting alive tokens -/
def testCountAliveTokens : IO Unit := do
  let (count0, count1, count2, count3, count4) ← Async.block do
    let root ← Std.CancellationContext.new
    let count0 ← root.countAliveTokens -- Root only

    -- Fork 3 children
    let child1 ← root.fork
    let child2 ← root.fork
    let _child3 ← root.fork
    let count1 ← root.countAliveTokens -- Root + 3 children = 4

    -- Cancel one child (and its subtree)
    child1.cancel .cancel
    Async.sleep 100
    let count2 ← root.countAliveTokens -- Root + 2 children = 3

    -- Fork a grandchild from child2
    let _grandchild ← child2.fork
    let count3 ← root.countAliveTokens -- Root + 2 children + 1 grandchild = 4

    -- Cancel root (should cancel everything)
    root.cancel .cancel
    Async.sleep 100
    let count4 ← root.countAliveTokens -- All cancelled = 0

    return (count0, count1, count2, count3, count4)

  IO.println s!"Initial (root only): {count0}"
  IO.println s!"After forking 3 children: {count1}"
  IO.println s!"After cancelling 1 child: {count2}"
  IO.println s!"After forking grandchild: {count3}"
  IO.println s!"After cancelling root: {count4}"

/--
info: Initial (root only): 1
After forking 3 children: 4
After cancelling 1 child: 3
After forking grandchild: 4
After cancelling root: 0
-/
#guard_msgs in
#eval testCountAliveTokens
