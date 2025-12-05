/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Time
public import Std.Internal.UV
public import Std.Internal.Async.Basic
public import Std.Internal.Async.Timer
public import Std.Sync.Context

public section

namespace Std
namespace Internal
namespace IO
namespace Async

/--
An asynchronous computation with cancellation support via a `Context`.
-/
@[expose] abbrev ContextAsync (α : Type) := ReaderT Context Async α

namespace ContextAsync

/--
Run a `ContextAsync` computation with a given context.
-/
@[inline]
protected def run (ctx : Context) (x : ContextAsync α) : Async α :=
  x ctx

/--
Create a `ContextAsync` from an `Async` computation.
-/
@[inline]
protected def lift (x : Async α) : ContextAsync α :=
  fun _ => x

/--
Get the current context.
-/
@[inline]
def getContext : ContextAsync Context :=
  fun ctx => pure ctx

/--
Fork a child context and run a computation within it.
-/
@[inline]
def fork (x : ContextAsync α) : ContextAsync α :=
  fun parent => do
    let child ← Context.fork parent
    x child

/--
Check if the current context is cancelled.
-/
@[inline]
def isCancelled : ContextAsync Bool := do
  let ctx ← getContext
  ctx.isCancelled

/--
Get the cancellation reason if the context is cancelled.
-/
@[inline]
def getCancellationReason : ContextAsync (Option CancellationReason) := do
  let ctx ← getContext
  ctx.getCancellationReason

/--
Cancel the current context with the given reason.
-/
@[inline]
def cancel (reason : CancellationReason) : ContextAsync Unit := do
  let ctx ← getContext
  ctx.cancel reason

/--
Wait for the current context to be cancelled.
-/
@[inline]
def doneSelector : ContextAsync (Selector Unit) := do
  let ctx ← getContext
  return ctx.doneSelector

/--
Wait for the current context to be cancelled.
-/
@[inline]
def awaitCancellation : ContextAsync Unit := do
  let ctx ← getContext
  let task ← ctx.done
  await task

/--
Run two computations concurrently and return both results. If either fails or is cancelled,
both are cancelled.
-/
@[inline, specialize]
def concurrently (x : ContextAsync α) (y : ContextAsync β)
    (prio := Task.Priority.default) : ContextAsync (α × β) := do
  let ctx ← getContext
  Async.concurrently (x ctx) (y ctx) prio

/--
Run two computations concurrently and return the result of the first to complete.
The loser's context is cancelled.
-/
@[inline, specialize]
def race [Inhabited α] (x : ContextAsync α) (y : ContextAsync α)
    (prio := Task.Priority.default) : ContextAsync α := do
  let parent ← getContext
  let ctx1 ← Context.fork parent
  let ctx2 ← Context.fork parent

  let task1 ← async (x ctx1) prio
  let task2 ← async (y ctx2) prio

  let result ← Async.race
    (await task1 <* ctx2.cancel .cancel)
    (await task2 <* ctx1.cancel .cancel)
    prio

  pure result

/--
Run all computations concurrently and collect results. If any fails or is cancelled,
all are cancelled.
-/
@[inline, specialize]
def concurrentlyAll (xs : Array (ContextAsync α))
    (prio := Task.Priority.default) : ContextAsync (Array α) := do
  let ctx ← getContext
  Async.concurrentlyAll (xs.map (· ctx)) prio

/--
Run all computations concurrently and return the first result. All losers are cancelled.
-/
@[inline, specialize]
def raceAll [ForM ContextAsync c (ContextAsync α)] (xs : c)
    (prio := Task.Priority.default) : ContextAsync α := do
  let parent ← getContext
  let promise ← IO.Promise.new

  ForM.forM xs fun x => do
    let ctx ← Context.fork parent
    let task ← async (x ctx) prio
    background do
      try
        let result ← await task
        -- Cancel parent to stop other tasks
        parent.cancel .cancel
        promise.resolve (.ok result)
      catch e =>
        -- Only set error if promise not already resolved
        discard $ promise.resolve (.error e)

  let result ← await promise
  Async.ofExcept result

/--
Run a computation in the background with its own forked context.
-/
@[inline]
def background (x : ContextAsync α) (prio := Task.Priority.default) : ContextAsync Unit := do
  let parent ← getContext
  let child ← Context.fork parent
  Async.background (x child) prio

instance : Functor ContextAsync where
  map f x := fun ctx => f <$> x ctx

instance : Monad ContextAsync where
  pure a := fun _ => pure a
  bind x f := fun ctx => x ctx >>= fun a => f a ctx

instance : MonadLift Async ContextAsync where
  monadLift := ContextAsync.lift

instance : MonadLift IO ContextAsync where
  monadLift x := fun _ => Async.ofIOTask (Task.pure <$> x)

instance : MonadLift BaseIO ContextAsync where
  monadLift x := fun _ => liftM (m := Async) x

instance : MonadExcept IO.Error ContextAsync where
  throw e := fun _ => throw e
  tryCatch x h := fun ctx => tryCatch (x ctx) (fun e => h e ctx)

instance : MonadFinally ContextAsync where
  tryFinally' x f := fun ctx =>
    tryFinally' (x ctx) (fun opt => f opt ctx)

instance [Inhabited α] : Inhabited (ContextAsync α) where
  default := fun _ => default

instance : MonadAwait AsyncTask ContextAsync where
  await t := fun _ => await t

instance : MonadAsync AsyncTask ContextAsync where
  async x prio := fun ctx => async (x ctx) prio

end ContextAsync

end Async
end IO
end Internal
end Std
