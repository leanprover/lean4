import Std.Internal.Async
import Std.Sync

open Std.Internal.IO Async

/-- Test ContextAsync cancellation check -/
def testIsCancelled : IO Unit := do
  let (before, after) ← Async.block do
    let ctx ← Std.CancellationContext.new
    ContextAsync.run ctx do
      let before ← ContextAsync.isCancelled
      ContextAsync.cancel .cancel
      Async.sleep 50
      let after ← ContextAsync.isCancelled
      return (before, after)

  IO.println s!"Before: {before}, After: {after}"

/--
info: Before: false, After: true
-/
#guard_msgs in
#eval testIsCancelled

/-- Test ContextAsync cancellation reason -/
def testGetCancellationReason : IO Unit := do
  let res ← Async.block do
    let ctx ← Std.CancellationContext.new
    ContextAsync.run ctx do
      ContextAsync.cancel (.custom "test reason")
      Async.sleep 50
      let some reason ← ContextAsync.getCancellationReason
        | return "ERROR: No reason found"
      return s!"Reason: {reason}"

  IO.println res

/--
info: Reason: custom("test reason")
-/
#guard_msgs in
#eval testGetCancellationReason

/-- Test awaitCancellation -/
def testAwaitCancellation : IO Unit := do
  let received ← Std.Mutex.new false

  Async.block do
    let ctx ← Std.CancellationContext.new
    let started ← Std.Mutex.new false

    ContextAsync.run ctx do
      discard <| ContextAsync.concurrently
        (do
          started.atomically (set true)
          ContextAsync.awaitCancellation
          received.atomically (set true))
        (do
          -- Wait for task to start
          while !(← started.atomically get) do
            Async.sleep 10

          Async.sleep 100
          ContextAsync.cancel .shutdown)

    Async.sleep 200

  let _ ← received.atomically get
  IO.println "Cancellation received"


def testSelectorCancellationFail : IO Unit := do
  let received ← Std.Mutex.new false

  let result ← Async.block do
    let ctx ← Std.CancellationContext.new
    let started ← Std.Mutex.new false


    let result ← do
      try
        ContextAsync.run ctx do
        discard <| ContextAsync.concurrently
          (do
            started.atomically (set true)
            let res ← Selectable.one #[
              .case (← ContextAsync.doneSelector) (fun _ => pure true),
              .case (← Selector.sleep 2000) (fun _ => pure false)
            ]
            received.atomically (set res))
          (do
            throw (.userError "failed")
            return ())
        return Except.ok ()
      catch err =>
        return Except.error err

    Async.sleep 500

    return result

  let _ ← received.atomically get
  IO.println "Cancellation received"

  if let Except.error err := result then
    throw err

/--
info: Cancellation received
---
error: failed
-/
#guard_msgs in
#eval testSelectorCancellationFail

/-- Test concurrently with both tasks succeeding -/
def testConcurrently : IO Unit := do
  let (a, b) ← Async.block do
    let ctx ← Std.CancellationContext.new
    ContextAsync.run ctx do
      ContextAsync.concurrently
        (do
          Async.sleep 100
          return 42)
        (do
          Async.sleep 150
          return "hello")

  IO.println s!"Results: {a}, {b}"

/--
info: Results: 42, hello
-/
#guard_msgs in
#eval testConcurrently

/-- Test race with first task winning -/
def testRace : IO Unit := do
  let result ← Async.block do
    let ctx ← Std.CancellationContext.new
    ContextAsync.run ctx do
      ContextAsync.race
        (do
          Async.sleep 50
          return "fast")
        (do
          Async.sleep 200
          return "slow")

  IO.println s!"Winner: {result}"

/--
info: Winner: fast
-/
#guard_msgs in
#eval testRace

/-- Test concurrentlyAll -/
def testConcurrentlyAll : IO Unit := do
  let results ← Async.block do
    let ctx ← Std.CancellationContext.new
    ContextAsync.run ctx do
      let tasks := #[
        (do Async.sleep 50; return 1),
        (do Async.sleep 100; return 2),
        (do Async.sleep 75; return 3)
      ]
      ContextAsync.concurrentlyAll tasks

  IO.println s!"All results: {results}"

/--
info: All results: #[1, 2, 3]
-/
#guard_msgs in
#eval testConcurrentlyAll

/-- Test background task with cancellation -/
def testBackground : IO Unit := do
  let counter ← Std.Mutex.new 0

  Async.block do
    let ctx ← Std.CancellationContext.new
    ContextAsync.run ctx do
      discard <| ContextAsync.concurrently
        (do
          for _ in [0:10] do
            if ← ContextAsync.isCancelled then
              break
            counter.atomically (modify (· + 1))
            Async.sleep 50)
        (do
          -- Let it run for a bit
          Async.sleep 150
          ContextAsync.cancel .cancel)

    Async.sleep 200

  let final ← counter.atomically get
  IO.println s!"Counter reached: {final}"

/-- Test fork cancellation isolation -/
def testForkCancellation : IO Unit := do
  let parent ← Std.CancellationContext.new
  let childCancelled ← Std.Mutex.new false
  let parentCancelled ← Std.Mutex.new false

  Async.block do
    ContextAsync.run parent do
      discard <| ContextAsync.concurrentlyAll #[
        (do
          let child ← ContextAsync.getContext
          Async.sleep 100
          child.cancel .cancel
          childCancelled.atomically (set true)),
        (do
        Async.sleep 200
        if ← parent.isCancelled then
          parentCancelled.atomically (set true))
      ]

  let childWasCancelled ← childCancelled.atomically get
  let parentWasCancelled ← parentCancelled.atomically get

  IO.println s!"Child cancelled: {childWasCancelled}, Parent cancelled: {parentWasCancelled}"

/--
info: Child cancelled: true, Parent cancelled: false
-/
#guard_msgs in
#eval testForkCancellation

/-- Test doneSelector -/
partial def testNestedFork : IO Unit := do
  let res ← Async.block do
    let ctx ← Std.CancellationContext.new

    ContextAsync.run ctx do
      let sel ← ContextAsync.doneSelector

      let (_, result) ← ContextAsync.concurrently
        (do
          Async.sleep 100
          ctx.cancel .deadline)
        (Selectable.one #[.case sel (fun _ => pure true)])

      return result

  IO.println s!"Done selector triggered: {res}"

/--
info: Done selector triggered: true
-/
#guard_msgs in
#eval testNestedFork

/-- Test Selector.cancelled -/
def testSelectorCancelled : IO Unit := do
  let res ← Async.block do
    let ctx ← Std.CancellationContext.new

    ContextAsync.run ctx do
      let sel ← Selector.cancelled

      let (_, result) ← ContextAsync.concurrently
        (do
          Async.sleep 150
          ctx.cancel .shutdown)
        (Selectable.one #[.case sel (fun _ => pure true)])

      return result

  IO.println s!"Selector.cancelled triggered: {res}"

/--
info: Selector.cancelled triggered: true
-/
#guard_msgs in
#eval testSelectorCancelled

/-- Test parent cancellation propagates to children -/
def testParentChildCancellation : IO Unit := do
  let parent ← Std.CancellationContext.new
  let childSawCancellation ← Std.Mutex.new false

  Async.block do
    ContextAsync.run parent do
      discard <| ContextAsync.concurrently
        (do

            ContextAsync.awaitCancellation
            childSawCancellation.atomically (set true))
        (do
          Async.sleep 200
          ContextAsync.cancel (.custom "parent cancel"))

    Async.sleep 300

  let childGotIt ← childSawCancellation.atomically get
  IO.println s!"Child saw parent cancellation: {childGotIt}"

/--
info: Child saw parent cancellation: true
-/
#guard_msgs in
#eval testParentChildCancellation

/-- Test MonadLift instances -/
def testMonadLift : IO Unit := do
  let (msg1, msg2) ← Async.block do
    let ctx ← Std.CancellationContext.new
    ContextAsync.run ctx do
      -- Lift from IO
      let msg1 : String := "From IO"

      -- Lift from BaseIO
      let msg2 : String := "From BaseIO"

      -- Lift from Async
      let _ ← (Async.sleep 50 : Async Unit)

      return (msg1, msg2)

  IO.println msg1
  IO.println msg2
  IO.println "All lifts work"

/--
info: From IO
From BaseIO
All lifts work
-/
#guard_msgs in
#eval testMonadLift

/-- Test exception handling in ContextAsync -/
def testExceptionHandling : IO Unit := do
  let res ← Async.block do
    let ctx ← Std.CancellationContext.new
    ContextAsync.run ctx do
      try
        throw (IO.userError "test error")
        return "Should not reach here"
      catch e =>
        return s!"Caught: {e}"

  IO.println res

/--
info: Caught: test error
-/
#guard_msgs in
#eval testExceptionHandling

/-- Test tryFinally in ContextAsync -/
def testTryFinally : IO Unit := do
  let cleaned ← Std.Mutex.new false

  Async.block do
    let ctx ← Std.CancellationContext.new
    ContextAsync.run ctx do
      try
        ContextAsync.cancel .cancel
        ContextAsync.awaitCancellation
      finally
        cleaned.atomically (set true)

  let wasCleanedUp ← cleaned.atomically get
  IO.println s!"Cleanup ran: {wasCleanedUp}"

/--
info: Cleanup ran: true
-/
#guard_msgs in
#eval testTryFinally

/-- Test race with cancellation -/
def testRaceWithCancellation : IO Unit := do
  let ctx ← Std.CancellationContext.new
  let leftCancelled ← Std.Mutex.new false
  let rightCancelled ← Std.Mutex.new false

  Async.block do
    ContextAsync.run ctx do
      let _ ← ContextAsync.race
        (do
          try
            Async.sleep 500
            return "left"
          finally
            if ← ContextAsync.isCancelled then
              leftCancelled.atomically (set true))
        (do
          try
            Async.sleep 50
            return "right"
          finally
            if ← ContextAsync.isCancelled then
              rightCancelled.atomically (set true))

      Async.sleep 1000

  let left ← leftCancelled.atomically get
  let right ← rightCancelled.atomically get
  IO.println s!"Left cancelled: {left}, Right cancelled: {right}"

/--
info: Left cancelled: true, Right cancelled: false
-/
#guard_msgs in
#eval testRaceWithCancellation

/-- Test complex concurrent workflow -/
def testComplexWorkflow : IO Unit := do
  let results ← Std.Mutex.new ([] : List String)

  Async.block do
    let ctx ← Std.CancellationContext.new

    ContextAsync.run ctx do
      -- Run multiple concurrent operations
      let (a, b) ← ContextAsync.concurrently
        (do
          Async.sleep 50
          results.atomically (modify ("A"::·))
          return 1)
        (do
          Async.sleep 75
          results.atomically (modify ("B"::·))
          return 2)

      -- Additional concurrent task
      discard <| ContextAsync.concurrently
        (do
          Async.sleep 100
          results.atomically (modify ("BG"::·)))
        (do
          Async.sleep 200
          results.atomically (modify (s!"Sum:{a+b}"::·)))

  let final ← results.atomically get
  IO.println s!"Results: {final.reverse}"

/--
info: Results: [A, B, BG, Sum:3]
-/
#guard_msgs in
#eval testComplexWorkflow

def testConcurrentlyAllException : IO Unit := do
  let ref ← IO.mkRef ""

  try
    Async.block do
      let ctx ← Std.CancellationContext.new
      ContextAsync.run ctx do
        let tasks := #[
          (do
            Async.sleep 1000
            if ← ContextAsync.isCancelled then
              ref.set "cancelled"
              return
            else
              ref.set "not cancelled"
            Async.sleep 500
            if ← ContextAsync.isCancelled then
              ref.modify (· ++ ", cancelled")
            else
              ref.modify (· ++ ", not cancelled")),
          (do
            Async.sleep 250
            throw (IO.userError "Error: Hello"))
        ]
        discard <| ContextAsync.concurrentlyAll tasks
  finally
    IO.println (← ref.get)

/--
info: cancelled
---
error: Error: Hello
-/
#guard_msgs in
#eval testConcurrentlyAllException
