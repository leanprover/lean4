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
cancellation propagation.

Features:
- Parent-child token relationships
- Bottom-up cancellation (children cancelled before parents)
- Asynchronous cancellation notifications with acknowledgments
- Safe propagation that avoids cancellation loops
-/

namespace Std
namespace Sync
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
  -/
  responsePromise : IO.Promise Bool

/--
Notify a consumer of cancellation and return a task for its response.
-/
private def Consumer.resolve (c : Consumer) (cancelled : Bool) : BaseIO (Task Bool) := do
  c.promise.resolve cancelled
  return c.responsePromise.result!

/--
Acknowledge or reject a cancellation request.
-/
private def Consumer.acknowledge (c : Consumer) (accepted : Bool) : BaseIO Unit :=
  c.responsePromise.resolve accepted

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
-/
def new : BaseIO CancellationToken := do
  let state ← Mutex.new {
    tokens := .empty |>.insert 0 {
      cancelled := false,
      parent := none,
      children := .empty,
      consumers := .empty,
      cancellationInProgress := false,
      cancellationInitiator := none
    }
    nextId := 1
    disposed := false
  }
  return ⟨state, 0⟩

/--
Create a child token from a parent.
The child is cancelled automatically if the parent is cancelled.
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
      cancellationInitiator := none
    }

    set {
      st with
      nextId := childId + 1,
      tokens := st.tokens.insert parent.id updatedParent |>.insert childId childInfo
    }

    return childId

  return ⟨parent.state, childId⟩

/--
Cancel a token, propagating bottom-up.

Process:
1. Mark token as cancelling and collect children
2. Recursively cancel children first
3. Notify and wait for consumers
4. Mark token as cancelled
-/
partial def cancel (source : CancellationToken) : EIO CancellationToken.Error Unit := do
  cancelBottomUp source.state source.id none
where
  cancelBottomUp (state : Mutex CancellationToken.State) (tokenId : Nat) (initiatorId : Option Nat) : EIO CancellationToken.Error Unit := do
    -- Phase 1: mark token and get children
    let (_, children) ← state.atomically do
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
      cancelBottomUp state childId (some tokenId)

    -- Phase 3: notify consumers and mark cancelled
    let responses ← state.atomically do
      let st ← get
      match st.tokens.get? tokenId with
      | none => return #[]
      | some tokenInfo =>
        let mut responseTasks := #[]
        for consumer in tokenInfo.consumers.toArray do
          let responseTask ← consumer.resolve true
          responseTasks := responseTasks.push responseTask

        let updatedInfo := {
          tokenInfo with
          cancelled := true,
          cancellationInProgress := false,
          consumers := .empty
        }
        set { st with tokens := st.tokens.insert tokenId updatedInfo }
        return responseTasks

    -- Phase 4: wait for responses
    for responseTask in responses do
      let _ := responseTask.get

/--
Check if a token is cancelled.
-/
def isCancelled (source : CancellationToken) : BaseIO Bool :=
  source.state.atomically do
    let st ← get
    match st.tokens.get? source.id with
    | none => return false
    | some tokenInfo => return tokenInfo.cancelled

/--
Dispose the token source, making all tokens invalid.
-/
def dispose (source : CancellationToken) : BaseIO Unit := do
  source.state.atomically do
    modify fun st => { st with disposed := true }

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
        let consumer : CancellationToken.Consumer := { promise, waiter := none, responsePromise }
        let updatedInfo := { tokenInfo with consumers := tokenInfo.consumers.enqueue consumer }
        set { st with tokens := st.tokens.insert token.id updatedInfo }

        let responseFunc := fun (accepted : Bool) => consumer.acknowledge accepted
        return (promise.result!, responseFunc)

/--
Wait for cancellation (simplified).
Returns a task that resolves when cancellation is requested.
-/
def waitForCancellation (token : CancellationToken) : BaseIO (Task Bool) := do
  let (task, _) ← token.waitForCancellationWithResponse
  return task

end CancellationToken
end Sync
end Std
