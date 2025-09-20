import Std.Internal.Async
import Std.Sync

open Std.Internal.IO Async

-- Test basic cancellation token creation and cancellation
def testBasicCancellation : Async Unit := do
  let token ← Std.CancellationToken.new

  assert! not (← token.isCancelled)

  token.cancel

  assert! (← token.isCancelled)

#eval testBasicCancellation.block

-- Test waitForCancellation functionality
def testWaitForCancellation : Async Unit := do
  let token ← Std.CancellationToken.new
  let completed ← Std.Mutex.new false

  -- Start a task that waits for cancellation
  let task ← async do
    let cancelTask ← token.waitForCancellation
    discard <| await cancelTask
    completed.atomically (set true)

  -- Verify not completed initially
  assert! not (← completed.atomically get)

  -- Cancel the token
  token.cancel

  -- Wait a bit for the task to complete
  Async.sleep 10
  await task

  -- Verify task completed
  assert! (← completed.atomically get)


-- Test fork functionality
def testFork : Async Unit := do
  let parentToken ← Std.CancellationToken.new
  let childToken ← parentToken.fork

  assert! not (← parentToken.isCancelled)
  assert! not (← childToken.isCancelled)

  -- Cancel parent, child should also be cancelled
  parentToken.cancel

  assert! (← parentToken.isCancelled)
  assert! (← childToken.isCancelled)

#eval testFork.block

-- Test independent child cancellation
def testIndependentChildCancellation : Async Unit := do
  let parentToken ← Std.CancellationToken.new
  let childToken ← parentToken.fork

  -- Cancel child, parent should remain active
  childToken.cancel

  assert! not (← parentToken.isCancelled)
  assert! (← childToken.isCancelled)

#eval testIndependentChildCancellation.block

-- Test multiple forks
def testMultipleForks : Async Unit := do
  let parentToken ← Std.CancellationToken.new
  let child1 ← parentToken.fork
  let child2 ← parentToken.fork
  let child3 ← parentToken.fork

  assert! not (← parentToken.isCancelled)
  assert! not (← child1.isCancelled)
  assert! not (← child2.isCancelled)
  assert! not (← child3.isCancelled)

  -- Cancel one child
  child2.cancel

  assert! not (← parentToken.isCancelled)
  assert! not (← child1.isCancelled)
  assert! (← child2.isCancelled)
  assert! not (← child3.isCancelled)

  -- Cancel parent
  parentToken.cancel

  assert! (← parentToken.isCancelled)
  assert! (← child1.isCancelled)
  assert! (← child2.isCancelled)
  assert! (← child3.isCancelled)

#eval testMultipleForks.block

-- Test nested forks (grandchildren)
def testNestedForks : Async Unit := do
  let rootToken ← Std.CancellationToken.new
  let childToken ← rootToken.fork
  let grandchildToken ← childToken.fork

  assert! not (← rootToken.isCancelled)
  assert! not (← childToken.isCancelled)
  assert! not (← grandchildToken.isCancelled)

  -- Cancel root, all descendants should be cancelled
  rootToken.cancel

  assert! (← rootToken.isCancelled)
  assert! (← childToken.isCancelled)
  assert! (← grandchildToken.isCancelled)

#eval testNestedForks.block

-- Test cancellation propagation with multiple levels
def testCancellationPropagation : Async Unit := do
  let rootToken ← Std.CancellationToken.new
  let level1a ← rootToken.fork
  let level1b ← rootToken.fork
  let level2a ← level1a.fork
  let level2b ← level1a.fork
  let level2c ← level1b.fork

  -- Cancel middle level token
  level1a.cancel

  -- Check that only level1a and its children are cancelled
  assert! not (← rootToken.isCancelled)
  assert! (← level1a.isCancelled)
  assert! not (← level1b.isCancelled)
  assert! (← level2a.isCancelled)
  assert! (← level2b.isCancelled)
  assert! not (← level2c.isCancelled)

#eval testCancellationPropagation.block

-- Test waitForCancellation with already cancelled token
def testWaitForCancellationAlreadyCancelled : Async Unit := do
  let token ← Std.CancellationToken.new
  token.cancel

  let completed ← Std.Mutex.new false

  -- Wait for cancellation on already cancelled token
  let cancelTask ← token.waitForCancellation
  let _task ← async do
    discard <| await cancelTask
    completed.atomically (set true)

  -- Should complete immediately
  Async.sleep 10
  assert! (← completed.atomically get)

#eval testWaitForCancellationAlreadyCancelled.block

-- Test multiple waiters on same token
def testMultipleWaiters : Async Unit := do
  let token ← Std.CancellationToken.new
  let completed1 ← Std.Mutex.new false
  let completed2 ← Std.Mutex.new false
  let completed3 ← Std.Mutex.new false

  -- Start multiple waiters
  let task1 ← async do
    let cancelTask ← token.waitForCancellation
    discard <| await cancelTask
    completed1.atomically (set true)

  let task2 ← async do
    let cancelTask ← token.waitForCancellation
    discard <| await cancelTask
    completed2.atomically (set true)

  let task3 ← async do
    let cancelTask ← token.waitForCancellation
    discard <| await cancelTask
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

#eval testMultipleWaiters.block

-- Test cancellation during async operations
def testCancellationDuringOperation : Async Unit := do
  let token ← Std.CancellationToken.new
  let operationStarted ← Std.Mutex.new false
  let operationCompleted ← Std.Mutex.new false
  let operationCancelled ← Std.Mutex.new false

  let task ← async do
    operationStarted.atomically (set true)
    try
      -- Simulate long-running operation
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

-- Test tree cancellation scenario (similar to your example)
partial def spawnTreeTest (counter : Std.Mutex Nat) (token : Std.CancellationToken) (depth : Nat) (path : String) : Async Unit := do
  let childToken ← token.fork
  counter.atomically (modify (· + 1))

  if depth == 0 then
    -- Leaf node - just wait for cancellation
    let cancelTask ← childToken.waitForCancellation
    discard <| await cancelTask
  else
    -- Internal node - spawn children and wait
    let leftTask ← async (spawnTreeTest counter childToken (depth - 1) (path ++ ".l"))
    let rightTask ← async (spawnTreeTest counter childToken (depth - 1) (path ++ ".r"))

    -- Wait for cancellation
    let cancelTask ← childToken.waitForCancellation
    discard <| await cancelTask

    -- Clean up children
    await leftTask
    await rightTask

def testTreeCancellation : Async Unit := do
  let rootToken ← Std.CancellationToken.new
  let counter ← Std.Mutex.new 0

  -- Spawn a tree of depth 3 (should create 2^3 - 1 = 7 internal nodes + 8 leaf nodes = 15 total)
  let treeTask ← async (spawnTreeTest counter rootToken 3 "root")

  -- Let the tree build up
  Async.sleep 50

  -- Verify we have the expected number of nodes
  let nodeCount ← counter.atomically get
  assert! nodeCount == 15 -- 2^4 - 1 = 15 nodes total for depth 3

  -- Cancel the entire tree
  rootToken.cancel

  -- Wait for tree to complete
  await treeTask

#eval testTreeCancellation.block

-- Test cancellation token reuse (should work)
def testTokenReuse : Async Unit := do
  let token ← Std.CancellationToken.new

  -- First use
  token.cancel
  assert! (← token.isCancelled)

  -- Create new token for second use
  let token2 ← Std.CancellationToken.new
  assert! not (← token2.isCancelled)

  token2.cancel
  assert! (← token2.isCancelled)

#eval testTokenReuse.block

-- Test complex hierarchy cancellation
def testComplexHierarchy : Async Unit := do
  let root ← Std.CancellationToken.new

  -- Create a complex hierarchy
  --       root
  --      /    \
  --   branch1  branch2
  --   /   \    /   \
  --  l1a  l1b l2a  l2b

  let branch1 ← root.fork
  let branch2 ← root.fork
  let leaf1a ← branch1.fork
  let leaf1b ← branch1.fork
  let leaf2a ← branch2.fork
  let leaf2b ← branch2.fork

  -- Cancel branch1, should affect leaf1a and leaf1b but not branch2 side
  branch1.cancel

  assert! not (← root.isCancelled)
  assert! (← branch1.isCancelled)
  assert! not (← branch2.isCancelled)
  assert! (← leaf1a.isCancelled)
  assert! (← leaf1b.isCancelled)
  assert! not (← leaf2a.isCancelled)
  assert! not (← leaf2b.isCancelled)

  -- Now cancel root, should affect everything remaining
  root.cancel

  assert! (← root.isCancelled)
  assert! (← branch1.isCancelled)  -- was already cancelled
  assert! (← branch2.isCancelled)
  assert! (← leaf1a.isCancelled)   -- was already cancelled
  assert! (← leaf1b.isCancelled)   -- was already cancelled
  assert! (← leaf2a.isCancelled)
  assert! (← leaf2b.isCancelled)

#eval testComplexHierarchy.block

-- Test edge case: fork from cancelled token
def testForkFromCancelledToken : Async Unit := do
  let parentToken ← Std.CancellationToken.new
  parentToken.cancel

  -- Fork from already cancelled token
  let childToken ← parentToken.fork

  -- Child should immediately be cancelled
  assert! (← parentToken.isCancelled)
  assert! (← childToken.isCancelled)

#eval testForkFromCancelledToken.block

-- Test performance with many tokens
def testManyTokens : Async Unit := do
  let tokens : Array Std.CancellationToken ← (Array.range 100).mapM (fun _ => Std.CancellationToken.new)

  -- Create forks
  let forks : Array Std.CancellationToken ← tokens.mapM (·.fork)

  -- Cancel all parent tokens
  for token in tokens do
    token.cancel

  -- Verify all forks are cancelled
  for fork in forks do
    assert! (← fork.isCancelled)

#eval testManyTokens.block
