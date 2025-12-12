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
public import Std.Sync.CancellationToken
public import Std.Internal.Async.Select

public section

/-!
This module provides a tree-structured cancellation context called `CancellationToken` where cancelling a parent
automatically cancels all child contexts.
-/

namespace Std
open Std.Internal.IO.Async

structure CancellationContext.State where
  /--
  Map of token IDs to optional tokens and their children.
  -/
  tokens : TreeMap UInt64 (CancellationToken × Array UInt64) := .empty

  /--
  Next available ID
  -/
  id : UInt64 := 1

/--
A cancellation context that allows multiple consumers to wait until cancellation is requested. Forms
a tree structure where cancelling a parent cancels all children.
-/
structure CancellationContext where
  state : Std.Mutex CancellationContext.State
  token : CancellationToken
  id : UInt64

namespace CancellationContext

/--
Creates a new root cancellation context.
-/
def new : BaseIO CancellationContext := do
  let token ← Std.CancellationToken.new
  return {
    state := ← Std.Mutex.new { tokens := .empty |>.insert 0 (token, #[]) },
    token,
    id := 0
  }

/--
Forks a child context from a parent. If the parent is already cancelled, returns the parent context.
Otherwise, creates a new child that will be cancelled when the parent is cancelled.
-/
def fork (root : CancellationContext) : BaseIO CancellationContext := do
  root.state.atomically do
    if ← root.token.isCancelled then
      return root

    let token ← Std.CancellationToken.new

    let st ← get
    let newId := st.id

    set { st with
      id := newId + 1,
      tokens := st.tokens.insert newId (token, #[])
        |>.modify root.id (.map (·) (.push · newId))
    }

    return { state := root.state, token, id := newId }

/--
Recursively cancels a context and all its children with the given reason.
-/
private partial def cancelChildren (state : CancellationContext.State) (id : UInt64) (reason : CancellationReason) : BaseIO CancellationContext.State := do
  let mut state := state

  let some (token, children) := state.tokens.get? id
    | return state

  for tokenId in children do
    state ← cancelChildren state tokenId reason

  token.cancel reason

  pure { state with tokens := state.tokens.erase id }

/--
Cancels this context and all child contexts with the given reason.
-/
def cancel (x : CancellationContext) (reason : CancellationReason) : BaseIO Unit := do
  if ← x.token.isCancelled then
    return

  x.state.atomically do
    let st ← get
    let st ← cancelChildren st x.id reason
    set st

/--
Checks if the context is cancelled.
-/
@[inline]
def isCancelled (x : CancellationContext) : BaseIO Bool := do
  x.token.isCancelled

/--
Returns the cancellation reason if the context is cancelled.
-/
@[inline]
def getCancellationReason (x : CancellationContext) : BaseIO (Option CancellationReason) := do
  x.token.getCancellationReason

/--
Waits for cancellation. Returns a task that completes when the context is cancelled.
-/
@[inline]
def done (x : CancellationContext) : IO (AsyncTask Unit) :=
  x.token.wait

/--
Creates a selector that waits for cancellation.
-/
@[inline]
def doneSelector (x : CancellationContext) : Selector Unit :=
  x.token.selector

private partial def countAliveTokensRec (state : CancellationContext.State) (id : UInt64) : Nat :=
  match state.tokens.get? id with
  | none => 0
  | some (_, children) => 1 + children.foldl (fun acc childId => acc + countAliveTokensRec state childId) 0

/--
Counts the number of alive (non-cancelled) tokens in the context tree, including
this context and all its descendants.
-/
def countAliveTokens (x : CancellationContext) : BaseIO Nat := do
  x.state.atomically do
    let st ← get
    return countAliveTokensRec st x.id

end CancellationContext
end Std
