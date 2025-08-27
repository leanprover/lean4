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
This module contains the implementation of `Std.Terminator` with bottom-up cancellation.
-/

namespace Std

/--
Errors that may be thrown while interacting with the terminator API.
-/
inductive Terminator.Error where
  | cancelled
  | alreadyCancelled
  | disposed
  | tokenNotFound

deriving Repr, DecidableEq, Hashable

instance instToStringTerminatorError : ToString Terminator.Error where
  toString
    | .cancelled => "operation was cancelled"
    | .alreadyCancelled => "token is already cancelled"
    | .disposed => "token has been disposed"
    | .tokenNotFound => "token ID not found"

instance instMonadLiftTerminatorIO : MonadLift (EIO Terminator.Error) IO where
  monadLift x := EIO.toIO (.userError <| toString ·) x

/--
A consumer waiting to receive a cancellation notification.
Enhanced to support awaiting cancellation response.
-/
private structure Terminator.Consumer where
  promise : IO.Promise Bool
  waiter : Option (Internal.IO.Async.Waiter Bool)
  responsePromise : IO.Promise Bool

/--
Resolves a consumer's promise and waits for response.
-/
private def Terminator.Consumer.resolve (c : Terminator.Consumer) (b : Bool) : BaseIO (Task Bool) := do
  c.promise.resolve b
  return c.responsePromise.result!

/--
Consumer acknowledges the cancellation request.
-/
private def Terminator.Consumer.acknowledge (c : Terminator.Consumer) (accepted : Bool) : BaseIO Unit :=
  c.responsePromise.resolve accepted

/--
Information about a terminator token in the tree.
-/
private structure TokenInfo where
  cancelled : Bool
  parent : Option Nat
  children : Std.TreeSet Nat
  consumers : Std.Queue Terminator.Consumer
  cancellationInProgress : Bool
  cancellationInitiator : Option Nat
deriving Inhabited

/--
State of the terminator system.
-/
private structure Terminator.State where
  tokens : Std.TreeMap Nat TokenInfo
  nextId : Nat
  disposed : Bool

/--
A terminator that can be checked for cancellation and register callbacks.
-/
structure Terminator where
  private mk ::
  private state : Mutex Terminator.State
  private id : Nat

/--
A terminator source that can create child tokens and trigger cancellation.
-/
structure Terminator.Source where
  private mk ::
  private state : Mutex Terminator.State
  private id : Nat

namespace Terminator.Source

/--
Creates a new root terminator source.
-/
def new : BaseIO Terminator.Source := do
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
Creates a child terminator source.
-/
def fork (parent : Terminator.Source) : IO Terminator.Source := do
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
Gets the terminator token for this source.
-/
def token (source : Terminator.Source) : Terminator :=
  ⟨source.state, source.id⟩

/--
Initiates bottom-up cancellation starting from this token.
First cancels all children, waits for their responses, then propagates up to parent.
-/
partial def cancel (source : Terminator.Source) : EIO Terminator.Error Unit := do
  cancelBottomUp source.state source.id none
where
  cancelBottomUp (state : Mutex Terminator.State) (tokenId : Nat) (initiatorId : Option Nat) : EIO Terminator.Error Unit := do
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

    for childId in children do
      cancelBottomUp state childId (some tokenId)

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

    for responseTask in responses do
      let response := responseTask.get
      if not response then
        pure ()

    match tokenInfo.parent with
    | none => pure ()
    | some parentId =>
      match initiatorId with
      | none => cancelBottomUp state parentId (some tokenId)
      | some initId =>
        if initId == parentId then pure ()
        else cancelBottomUp state parentId (some tokenId)

/--
Checks if this token source exists and is cancelled.
-/
def isCancelled (source : Terminator.Source) : BaseIO Bool :=
  source.state.atomically do
    let st ← get
    match st.tokens.get? source.id with
    | none => return false
    | some tokenInfo => return tokenInfo.cancelled

/--
Disposes the token source and all its children.
-/
def dispose (source : Terminator.Source) : BaseIO Unit := do
  source.state.atomically do
    modify fun st => { st with disposed := true }

end Terminator.Source

namespace Terminator

/--
Creates a new root terminator.
-/
def new : BaseIO Terminator := do
  let source ← Terminator.Source.new
  return source.token

/--
Creates a child terminator.
-/
def fork (parent : Terminator) : IO Terminator := do
  let parentSource : Terminator.Source := ⟨parent.state, parent.id⟩
  let childSource ← parentSource.fork
  return childSource.token

/--
Checks if this token is cancelled.
-/
def isCancelled (token : Terminator) : BaseIO Bool :=
  token.state.atomically do
    let st ← get
    match st.tokens.get? token.id with
    | none => return true  -- Token was removed
    | some tokenInfo => return tokenInfo.cancelled

/--
Throws if cancelled.
-/
def throwIfCancelled (token : Terminator) : EIO Terminator.Error Unit := do
  if ← token.isCancelled then
    throw .cancelled

/--
Enhanced cancellation waiting that allows responding to cancellation requests.
Returns a task and a function to respond to cancellation.
-/
def waitForCancellationWithResponse (token : Terminator) : BaseIO (Task Bool × (Bool → BaseIO Unit)) := do
  token.state.atomically do
    let st ← get
    if st.disposed then
      return (.pure false, fun _ => pure ())

    match st.tokens.get? token.id with
    | none => return (.pure true, fun _ => pure ())  -- Already cancelled
    | some tokenInfo =>
      if tokenInfo.cancelled then
        return (.pure true, fun _ => pure ())
      else
        let promise ← IO.Promise.new
        let responsePromise ← IO.Promise.new
        let consumer : Terminator.Consumer := { promise, waiter := none, responsePromise }
        let updatedInfo := { tokenInfo with consumers := tokenInfo.consumers.enqueue consumer }
        set { st with tokens := st.tokens.insert token.id updatedInfo }

        let responseFunc := fun (accepted : Bool) => consumer.acknowledge accepted
        return (promise.result!, responseFunc)

/--
Original wait function for backward compatibility.
-/
def waitForCancellation (token : Terminator) : BaseIO (Task Bool) := do
  let (task, _) ← token.waitForCancellationWithResponse
  return task

end Terminator

end Std
