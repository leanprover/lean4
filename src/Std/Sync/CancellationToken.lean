/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Data
public import Init.System.Promise
public import Init.Data.Queue
public import Std.Sync.Mutex
public import Std.Internal.Async.Select

public section

/-!
This module implements a hierarchical cancellation token system with bottom-up
cancellation propagation and automatic cleanup.

Features:
- Parent-child token relationships
- Bottom-up cancellation (children cancelled before parents)
- Asynchronous cancellation notifications with acknowledgments
- Safe propagation that avoids cancellation loops
- Automatic cleanup of cancelled tokens from the tree
-/

namespace Std
namespace CancellationToken

/--
Errors that can occur when working with cancellation tokens.
-/
inductive Error where

  /--
  The operation was cancelled.
  -/
  | cancelled

  /--
  The token is already cancelled.
  -/
  | alreadyCancelled

  /--
  The token has been disposed and is no longer valid.
  -/
  | disposed

  /--
  The given token ID was not found in the token tree.
  -/
  | tokenNotFound

deriving Repr, DecidableEq, Hashable

namespace Error

instance : ToString Error where
  toString
    | .cancelled => "operation was cancelled"
    | .alreadyCancelled => "token is already cancelled"
    | .disposed => "token has been disposed"
    | .tokenNotFound => "token ID not found"

instance : MonadLift (EIO Error) IO where
  monadLift x := EIO.toIO (.userError <| toString ·) x

end Error

/--
A consumer that waits for cancellation and can respond to it.
-/
private structure Consumer where

  /--
  Promise resolved when cancellation is requested.
  -/
  promise : IO.Promise Bool

  /--
  Optional waiter for async operations.
  -/
  waiter : Option (Internal.IO.Async.Waiter Bool)

  /--
  Promise for the consumer's acknowledgment of cancellation.
  If None, no acknowledgment is expected (fire-and-forget).
  -/
  responsePromise : Option (IO.Promise Bool)

/--
Notify a consumer of cancellation.
For consumers with acknowledgment, return a task for the response.
For fire-and-forget consumers, return a completed task.
-/
private def Consumer.resolve (c : Consumer) (cancelled : Bool) : BaseIO (Task Bool) := do
  c.promise.resolve cancelled
  match c.responsePromise with
  | some rp => return rp.result!
  | none => return Task.pure true  -- Fire-and-forget, immediately acknowledge

/--
Acknowledge or reject a cancellation request.
Only works if the consumer was created with acknowledgment support.
-/
private def Consumer.acknowledge (c : Consumer) (accepted : Bool) : BaseIO Unit :=
  match c.responsePromise with
  | some rp => rp.resolve accepted
  | none => pure ()  -- No-op for fire-and-forget consumers

/--
Internal state for a token in the tree.
-/
private structure TokenInfo where

  /--
  Whether this token is cancelled.
  -/
  cancelled : Bool

  /--
  Parent token ID (none if root).
  -/
  parent : Option Nat

  /--
  Set of child token IDs.
  -/
  children : Std.TreeSet Nat

  /--
  Consumers waiting for cancellation notifications.
  -/
  consumers : Std.Queue Consumer

  /--
  Whether cancellation is currently in progress.
  -/
  cancellationInProgress : Bool

  /--
  ID of the initiator token (to prevent loops).
  -/
  cancellationInitiator : Option Nat

  /--
  Whether this token should be cleaned up after cancellation.
  Root tokens are typically not cleaned up automatically.
  -/
  cleanupAfterCancel : Bool
deriving Inhabited

/--
Global state for the cancellation token system.
-/
private structure State where

  /--
  Mapping from token ID to its info.
  -/
  tokens : Std.TreeMap Nat TokenInfo

  /--
  Next available token ID.
  -/
  nextId : Nat

  /--
  Whether the system has been disposed.
  -/
  disposed : Bool

  /--
  Tokens scheduled for cleanup (processed asynchronously to avoid blocking cancellation).
  -/
  cleanupQueue : Std.Queue Nat

end CancellationToken

/--
A cancellation token that can be observed for cancellation.
Tokens form a tree with bottom-up propagation.
-/
structure CancellationToken where
  private mk ::
  private state : Mutex CancellationToken.State
  private id : Nat

namespace CancellationToken

/--
Create a new root cancellation token.
Root tokens are not automatically cleaned up when cancelled.
-/
def new : BaseIO CancellationToken := do
  let state ← Mutex.new {
    tokens := .empty |>.insert 0 {
      cancelled := false,
      parent := none,
      children := .empty,
      consumers := .empty,
      cancellationInProgress := false,
      cancellationInitiator := none,
      cleanupAfterCancel := false  -- Root tokens are not auto-cleaned
    }
    nextId := 1
    disposed := false
    cleanupQueue := .empty
  }
  return ⟨state, 0⟩

/--
Create a child token from a parent.
The child is cancelled automatically if the parent is cancelled.
Child tokens are automatically cleaned up after cancellation.
-/
def fork (parent : CancellationToken) : IO CancellationToken := do
  let childId ← parent.state.atomically do
    let st ← get
    if st.disposed then
      throw (.userError "token source is disposed")

    let childId := st.nextId
    let parentInfo := st.tokens.get! parent.id

    let updatedParent := { parentInfo with children := parentInfo.children.insert childId }

    let childInfo : TokenInfo := {
      cancelled := parentInfo.cancelled,
      parent := some parent.id,
      children := .empty,
      consumers := .empty,
      cancellationInProgress := false,
      cancellationInitiator := none,
      cleanupAfterCancel := true  -- Child tokens are auto-cleaned
    }

    set {
      st with
      nextId := childId + 1,
      tokens := st.tokens.insert parent.id updatedParent |>.insert childId childInfo
    }

    return childId

  return ⟨parent.state, childId⟩

/--
Remove a token from the tree and clean up references.
This is called after a token has been cancelled and all consumers notified.
-/
private def cleanupToken (state : Mutex CancellationToken.State) (tokenId : Nat) : BaseIO Unit := do
  state.atomically do
    let st ← get
    match st.tokens.get? tokenId with
    | none => return ()
    | some tokenInfo =>
      let updatedTokens :=
        match tokenInfo.parent with
        | some pId =>
          match st.tokens.get? pId with
          | none => st.tokens.erase tokenId
          | some parentInfo =>
            let updatedParent := { parentInfo with children := parentInfo.children.erase tokenId }
            st.tokens.insert pId updatedParent |>.erase tokenId
        | none => st.tokens.erase tokenId

      let updatedCleanupQueue := tokenInfo.children.foldl (·.enqueue ·) st.cleanupQueue

      set {
        st with
        tokens := updatedTokens,
        cleanupQueue := updatedCleanupQueue
      }

/--
Process the cleanup queue, removing cancelled tokens that are eligible for cleanup.
This runs asynchronously to avoid blocking the cancellation process.
-/
private def processCleanupQueue (state : Mutex CancellationToken.State) : BaseIO Unit := do
  let batchSize := 10
  for _ in [0:batchSize] do
    let tokenIdOpt ← state.atomically do
      let st ← get
      match st.cleanupQueue.dequeue? with
      | none => return none
      | some (tokenId, newQueue) =>
        set { st with cleanupQueue := newQueue }
        return some tokenId

    match tokenIdOpt with
    | none => break
    | some tokenId =>
      let shouldCleanup ← state.atomically do
        let st ← get
        match st.tokens.get? tokenId with
        | none => return false
        | some tokenInfo =>
          return tokenInfo.cancelled &&
                 tokenInfo.cleanupAfterCancel &&
                 not tokenInfo.cancellationInProgress &&
                 tokenInfo.consumers.isEmpty

      if shouldCleanup then
        cleanupToken state tokenId

/--
Cancel a token, propagating bottom-up, with automatic cleanup.

zProcess:
1. Mark token as cancelling and collect children
2. Recursively cancel children first
3. Notify consumers (fire-and-forget for simple consumers)
4. Mark token as cancelled
5. Schedule cleanup for eligible tokens
-/
partial def cancel (source : CancellationToken) : EIO CancellationToken.Error Unit := do
  cancelBottomUp source.state source.id none
  -- Process cleanup queue after cancellation is complete
  processCleanupQueue source.state
where
  cancelBottomUp (state : Mutex CancellationToken.State) (tokenId : Nat) (initiatorId : Option Nat) : EIO CancellationToken.Error Unit := do
    -- Phase 1: mark token and get children
    let (tokenInfo, children) ← state.atomically do
      let st ← get
      if st.disposed then
        throw .disposed

      match st.tokens.get? tokenId with
      | none => throw .tokenNotFound
      | some tokenInfo =>
        if tokenInfo.cancelled then
          throw .alreadyCancelled

        let updatedInfo := {
          tokenInfo with
          cancellationInProgress := true,
          cancellationInitiator := initiatorId
        }
        set { st with tokens := st.tokens.insert tokenId updatedInfo }
        return (tokenInfo, tokenInfo.children.toArray)

    -- Phase 2: cancel children
    for childId in children do
      try
        cancelBottomUp state childId (some tokenId)
      catch e =>
        -- Continue cancelling other children even if one fails
        continue

    -- Phase 3: notify consumers and mark cancelled
    let responses ← state.atomically do
      let st ← get
      match st.tokens.get? tokenId with
      | none => return #[]
      | some tokenInfo =>
        let mut responseTasks := #[]
        for consumer in tokenInfo.consumers.toArray do
          try
            let responseTask ← consumer.resolve true
            -- Only collect tasks that actually need acknowledgment
            match consumer.responsePromise with
            | some _ => responseTasks := responseTasks.push responseTask
            | none => pure ()  -- Fire-and-forget, no need to wait
          catch e =>
            -- Continue with other consumers even if one fails
            continue

        let updatedInfo := {
          tokenInfo with
          cancelled := true,
          cancellationInProgress := false,
          consumers := .empty
        }
        set { st with tokens := st.tokens.insert tokenId updatedInfo }
        return responseTasks

    -- Phase 4: wait for responses (only from consumers that require acknowledgment)
    for responseTask in responses do
      try
        let _ := responseTask.get
      catch e =>
        -- Consumer didn't acknowledge properly, continue anyway
        continue

    -- Phase 5: schedule cleanup if eligible
    if tokenInfo.cleanupAfterCancel then
      state.atomically do
        modify fun st => { st with cleanupQueue := st.cleanupQueue.enqueue tokenId }

/--
Check if a token is cancelled.
-/
def isCancelled (source : CancellationToken) : BaseIO Bool :=
  source.state.atomically do
    let st ← get
    match st.tokens.get? source.id with
    | none => return true  -- If token is not found, consider it cancelled (cleaned up)
    | some tokenInfo => return tokenInfo.cancelled

/--
Explicitly clean up a cancelled token.
This can be called manually to clean up tokens immediately rather than waiting
for the automatic cleanup process.
-/
def cleanup (source : CancellationToken) : BaseIO Unit := do
  let shouldCleanup ← source.state.atomically do
    let st ← get
    match st.tokens.get? source.id with
    | none => return false  -- Already cleaned up
    | some tokenInfo =>
      return tokenInfo.cancelled &&
             not tokenInfo.cancellationInProgress &&
             tokenInfo.consumers.isEmpty

  if shouldCleanup then
    cleanupToken source.state source.id

/--
Force cleanup of all eligible tokens in the cleanup queue.
This can be called periodically for maintenance.
-/
partial def forceCleanup (source : CancellationToken) : BaseIO Unit := do
  -- Process the entire cleanup queue
  let rec processAll : BaseIO Unit := do
    let hasMore ← source.state.atomically do
      let st ← get
      return not st.cleanupQueue.isEmpty

    if hasMore then
      processCleanupQueue source.state
      processAll

  processAll

/--
Dispose the token source, making all tokens invalid and cleaning up all state.
-/
def dispose (source : CancellationToken) : BaseIO Unit := do
  source.state.atomically do
    modify fun st => {
      st with
      disposed := true,
      tokens := .empty,  -- Clean up all tokens
      cleanupQueue := .empty
    }

/--
Throw if the token is cancelled.
Useful at the start of cancellable operations.
-/
def throwIfCancelled (token : CancellationToken) : EIO CancellationToken.Error Unit := do
  if ← token.isCancelled then
    throw .cancelled

/--
Register for cancellation with acknowledgment.

Returns:
- A task that completes when cancellation is requested
- A function to acknowledge the request
-/
def waitForCancellationWithResponse (token : CancellationToken) : BaseIO (Task Bool × (Bool → BaseIO Unit)) := do
  token.state.atomically do
    let st ← get
    if st.disposed then
      return (.pure false, fun _ => pure ())

    match st.tokens.get? token.id with
    | none =>
      return (.pure true, fun _ => pure ())
    | some tokenInfo =>
      if tokenInfo.cancelled then
        return (.pure true, fun _ => pure ())
      else
        let promise ← IO.Promise.new
        let responsePromise ← IO.Promise.new
        let consumer : CancellationToken.Consumer := {
          promise,
          waiter := none,
          responsePromise := some responsePromise
        }
        let updatedInfo := { tokenInfo with consumers := tokenInfo.consumers.enqueue consumer }
        set { st with tokens := st.tokens.insert token.id updatedInfo }

        let responseFunc := fun (accepted : Bool) => consumer.acknowledge accepted
        return (promise.result!, responseFunc)

/--
Wait for cancellation (simplified, fire-and-forget).
Returns a task that resolves when cancellation is requested.
No acknowledgment is required or expected.
-/
def waitForCancellation (token : CancellationToken) : BaseIO (Task Bool) := do
  token.state.atomically do
    let st ← get
    if st.disposed then
      return .pure false

    match st.tokens.get? token.id with
    | none =>
      return .pure true
    | some tokenInfo =>
      if tokenInfo.cancelled then
        return .pure true
      else
        let promise ← IO.Promise.new
        let consumer : CancellationToken.Consumer := {
          promise,
          waiter := none,
          responsePromise := none  -- Fire-and-forget, no response expected
        }
        let updatedInfo := { tokenInfo with consumers := tokenInfo.consumers.enqueue consumer }
        set { st with tokens := st.tokens.insert token.id updatedInfo }

        return promise.result!

end CancellationToken
end Std
