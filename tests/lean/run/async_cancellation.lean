import Std.Internal.Async
import Std.Sync

open Std.Internal.IO Async

def cancellableSelector [Monad m] [MonadLift IO m] [MonadAsync AsyncTask m] (fn : Std.CancellationToken → m α) : m (Selector (Except IO.Error α)) := do
  let signal ← Std.CancellationToken.new
  let promise ← IO.Promise.new
  let result : AsyncTask α ← async (fn signal)

  IO.chainTask result (promise.resolve ·)

  return {
    tryFn := do
      if ← promise.isResolved
        then return promise.result!.get
        else return none

    registerFn := fun waiter => do
      discard <| IO.mapTask (t := promise.result?) fun
        | none => pure ()
        | some res => do
          if ¬ (← signal.isCancelled) then
            waiter.race (pure ()) (·.resolve (.ok res))

    unregisterFn := do
      signal.cancel
  }

-- Test basic cancellation token creation and cancellation
def testBasicCancellation : Async Unit := do
  let token ← Std.CancellationToken.new
  assert! not (← token.isCancelled)
  token.cancel
  assert! (← token.isCancelled)

#eval testBasicCancellation.block

-- Test selector functionality
def testSelector : Async Unit := do
  let token ← Std.CancellationToken.new
  let completed ← Std.Mutex.new false

  let task ← async do
    Selectable.one #[.case token.selector (fun _ => pure ())]
    completed.atomically (set true)

  assert! not (← completed.atomically get)

  token.cancel
  await task

  assert! (← completed.atomically get)

#eval testSelector.block

-- Test selector with already cancelled token
def testSelectorAlreadyCancelled : Async Unit := do
  let token ← Std.CancellationToken.new
  token.cancel

  let completed ← Std.Mutex.new false

  let task ← async do
    Selectable.one #[.case token.selector pure]
    completed.atomically (set true)

  await task
  assert! (← completed.atomically get)

#eval testSelectorAlreadyCancelled.block

-- Test multiple selectors on same token
def testMultipleSelectors : Async Unit := do
  let token ← Std.CancellationToken.new
  let completed1 ← Std.Mutex.new false
  let completed2 ← Std.Mutex.new false
  let completed3 ← Std.Mutex.new false

  let task1 ← async do
    Selectable.one #[.case token.selector pure]
    completed1.atomically (set true)

  let task2 ← async do
    Selectable.one #[.case token.selector pure]
    completed2.atomically (set true)

  let task3 ← async do
    Selectable.one #[.case token.selector pure]
    completed3.atomically (set true)

  -- Verify none completed initially
  assert! not (← completed1.atomically get)
  assert! not (← completed2.atomically get)
  assert! not (← completed3.atomically get)

  -- Cancel token
  token.cancel

  -- Wait for all tasks to complete
  await task1
  await task2
  await task3

  -- Verify all completed
  assert! (← completed1.atomically get)
  assert! (← completed2.atomically get)
  assert! (← completed3.atomically get)

#eval testMultipleSelectors.block

-- Test cancellation during async operations
def testCancellationDuringOperation : Async Unit := do
  let token ← Std.CancellationToken.new
  let operationStarted ← Std.Mutex.new false
  let operationCompleted ← Std.Mutex.new false
  let operationCancelled ← Std.Mutex.new false

  let task ← async do
    operationStarted.atomically (set true)
    try
      for _ in List.range 100 do
        if (← token.isCancelled) then
          operationCancelled.atomically (set true)
          return
        Async.sleep 5
      operationCompleted.atomically (set true)
    catch _ =>
      operationCancelled.atomically (set true)

  -- Wait for operation to start
  while not (← operationStarted.atomically get) do
    Async.sleep 1

  -- Cancel after operation started
  Async.sleep 20
  token.cancel

  await task

  -- Verify operation was cancelled, not completed
  assert! (← operationStarted.atomically get)
  assert! (← operationCancelled.atomically get)
  assert! not (← operationCompleted.atomically get)

#eval testCancellationDuringOperation.block

-- Test token reuse (create new tokens)
def testTokenReuse : Async Unit := do
  let token1 ← Std.CancellationToken.new

  -- First use
  token1.cancel
  assert! (← token1.isCancelled)

  -- Create new token for second use
  let token2 ← Std.CancellationToken.new
  assert! not (← token2.isCancelled)

  token2.cancel
  assert! (← token2.isCancelled)

#eval testTokenReuse.block

-- Test performance with many tokens
def testManyTokens : Async Unit := do
  let tokens : Array Std.CancellationToken ← (Array.range 100).mapM (fun _ => Std.CancellationToken.new)

  -- All should start unresolved
  for token in tokens do
    assert! not (← token.isCancelled)

  -- Cancel all tokens
  for token in tokens do
    token.cancel

  -- Verify all are cancelled
  for token in tokens do
    assert! (← token.isCancelled)

#eval testManyTokens.block

-- Test cooperative cancellation pattern
def cooperativeWork (token : Std.CancellationToken) (workDone : Std.Mutex Nat) : Async Unit := do
  for _ in List.range 50 do
    -- Check for cancellation before each work unit
    if ← token.isCancelled then
      return

    -- Do some work
    workDone.atomically (modify (· + 1))
    Async.sleep 10

def testCooperativeCancellation : Async Unit := do
  let token ← Std.CancellationToken.new
  let workDone ← Std.Mutex.new 0

  -- Start cooperative work
  let workTask ← async (cooperativeWork token workDone)

  -- Let some work happen
  Async.sleep 150

  -- Cancel the work
  token.cancel

  await workTask

  -- Verify some but not all work was done
  let finalCount ← workDone.atomically get
  assert! finalCount > 0
  assert! finalCount < 50

#eval testCooperativeCancellation.block

-- Test selector with other operations
def testSelectorMixed : Async Unit := do
  let token ← Std.CancellationToken.new
  let result ← Std.Mutex.new ""

  let task ← async do
    let selected ← Selectable.one #[
      .case token.selector (fun _ => pure "cancelled")
    ]
    result.atomically (set selected)

  -- Race between promise resolution and cancellation
  Async.sleep 50
  token.cancel

  await task

  let finalResult ← result.atomically get
  assert! finalResult == "cancelled"

#eval testSelectorMixed.block

-- Test immediate cancellation
def testImmediateCancellation : Async Unit := do
  let token ← Std.CancellationToken.new

  -- Cancel immediately
  token.cancel

  -- Should be resolved right away
  assert! (← token.isCancelled)

  -- Selector should work with already cancelled token
  let task ← async do
    Selectable.one #[.case token.selector pure]
    return "done"

  let result ← await task
  assert! result == "done"

#eval testImmediateCancellation.block
