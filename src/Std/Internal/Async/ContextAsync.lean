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
public import Std.Sync.CancellationContext

public section

/-!
This module contains the implementation of `ContextAsync`, a monad for asynchronous computations with
cooperative cancellation support that must be explicitly checked for and cancelled explicitly.
-/

namespace Std
namespace Internal
namespace IO
namespace Async

/--
An asynchronous computation with cooperative cancellation support via a `CancellationContext`. `ContextAsync α`
is equivalent to `ReaderT CancellationContext Async α`, providing a `CancellationContext` value to async
computations.
-/
abbrev ContextAsync (α : Type) := ReaderT CancellationContext Async α

namespace ContextAsync

/--
Runs a `ContextAsync` computation with a given context. See also `ContextAsync.run` for running with a new
context that automatically cancels after execution.
-/
@[inline]
protected def runIn (ctx : CancellationContext) (x : ContextAsync α) : Async α :=
  x ctx

/--
Runs a `ContextAsync` computation with a new context that cancels after the execution of the computation.
See also `ContextAsync.runIn` for running with an existing context.
-/
@[inline]
protected def run (x : ContextAsync α) : Async α := do
  let ctx ← CancellationContext.new
  x ctx <* ctx.cancel .cancel

/--
Returns the current context for inspection or to pass to other functions.
-/
@[inline]
def getContext : ContextAsync CancellationContext :=
  fun ctx => pure ctx

/--
Checks if the current context is cancelled. Returns `true` if the context (or any ancestor) has been cancelled.
Long-running operations should periodically check this and exit gracefully when cancelled.
-/
@[inline]
def isCancelled : ContextAsync Bool := do
  let ctx ← getContext
  ctx.isCancelled

/--
Gets the cancellation reason if the context is cancelled. Returns `some reason` if cancelled, `none` otherwise,
allowing you to distinguish between different cancellation types.
-/
@[inline]
def getCancellationReason : ContextAsync (Option CancellationReason) := do
  let ctx ← getContext
  ctx.getCancellationReason

/--
Cancels the current context with the given reason, cascading to all child contexts.
Cancellation is cooperative, operations must explicitly check `isCancelled` or use `awaitCancellation` to respond.
-/
@[inline]
def cancel (reason : CancellationReason) : ContextAsync Unit := do
  let ctx ← getContext
  ctx.cancel reason

/--
Returns a selector that completes when the current context is cancelled.
-/
@[inline]
def doneSelector : ContextAsync (Selector Unit) := do
  let ctx ← getContext
  return ctx.doneSelector

/--
Waits for the current context to be cancelled.
-/
@[inline]
def awaitCancellation : ContextAsync Unit := do
  let ctx ← getContext
  let task ← ctx.done
  await task

/--
Runs two computations concurrently and returns both results. Each computation runs in its own child context;
if either fails or is cancelled, both are cancelled immediately and the exception is propagated.
-/
@[inline, specialize]
def concurrently (x : ContextAsync α) (y : ContextAsync β)
    (prio := Task.Priority.default) : ContextAsync (α × β) := do

  let ctx ← getContext
  let concurrentCtx ← ctx.fork

  let childCtx1 ← concurrentCtx.fork
  let childCtx2 ← concurrentCtx.fork

  let result ← Async.concurrently
    (try x childCtx1 catch err => do concurrentCtx.cancel .cancel; throw err finally childCtx1.cancel .cancel)
    (try y childCtx2 catch err => do concurrentCtx.cancel .cancel; throw err finally childCtx2.cancel .cancel)
    prio

  concurrentCtx.cancel .cancel
  return result

/--
Runs two computations concurrently and returns the result of the first to complete. Each computation runs
in its own child context; when either completes, the other is cancelled immediately.
-/
@[inline, specialize]
def race [Inhabited α] (x : ContextAsync α) (y : ContextAsync α)
    (prio := Task.Priority.default) : ContextAsync α := do
  let parent ← getContext
  let ctx1 ← CancellationContext.fork parent
  let ctx2 ← CancellationContext.fork parent

  let task1 ← async (x ctx1) prio
  let task2 ← async (y ctx2) prio

  let result ← Async.race
    (await task1 <* ctx2.cancel .cancel)
    (await task2 <* ctx1.cancel .cancel)
    prio

  pure result

/--
Runs all computations concurrently and collects results in the same order. Each runs in its own child context;
if any computation fails, all others are cancelled and the exception is propagated.
-/
@[inline, specialize]
def concurrentlyAll (xs : Array (ContextAsync α))
    (prio := Task.Priority.default) : ContextAsync (Array α) := do
  let ctx ← getContext
  let concurrentCtx ← ctx.fork

  let tasks : Array (AsyncTask α) ← xs.mapM fun ctxAsync => do
    let childCtx ← concurrentCtx.fork
    async (prio := prio)
      (try
        ctxAsync childCtx
      catch err => do
        concurrentCtx.cancel .cancel
        throw err
      finally
        childCtx.cancel .cancel)

  let result ← tasks.mapM await
  return result

/--
Launches a `ContextAsync` computation in the background, discarding its result.

The computation runs independently in the background in its own child context. The parent computation does not wait
for background tasks to complete. This means that if the parent finishes its execution it will cause
the cancellation of the background functions. See also `disown` for launching tasks that continue independently
even after parent cancellation.
-/
@[inline, specialize]
def background (action : ContextAsync α) (prio := Task.Priority.default) : ContextAsync Unit := do
  let ctx ← getContext
  let childCtx ← ctx.fork
  Async.background (action childCtx *> childCtx.cancel .cancel) prio

/--
Launches a `ContextAsync` computation in the background, discarding its result. It's similar to `background`,
but the child context is not automatically cancelled when the action completes. This allows the disowned
computation to continue running independently, even if the parent context is cancelled. The child context
will remain alive as long as the computation needs it. See also `background` for launching tasks that are
cancelled when the parent finishes.
-/
@[inline, specialize]
def disown (action : ContextAsync α) (prio := Task.Priority.default) : ContextAsync Unit := do
  let childCtx ← CancellationContext.new
  Async.background (action childCtx) prio

/--
Runs all computations concurrently and returns the first result. Each computation runs in its own child context;
when the first completes successfully, all others are cancelled immediately.
-/
def raceAll [ForM ContextAsync c (ContextAsync α)] (xs : c)
    (prio := Task.Priority.default) : ContextAsync α := do
  let parent ← getContext
  let promise ← IO.Promise.new

  ForM.forM xs fun x => do
    let ctx ← CancellationContext.fork parent
    let task ← async (x ctx) prio

    background do
      try
        let result ← await task
        promise.resolve (.ok result)
      catch e =>
        discard $ promise.resolve (.error e)

  let result ← await promise
  parent.cancel .cancel
  Async.ofExcept result

/--
Launches a `ContextAsync` computation as an asynchronous task with a forked child context.
The child context is automatically cancelled when the task completes or fails.
-/
@[inline, specialize]
def async (x : ContextAsync α) (prio := Task.Priority.default) : ContextAsync (AsyncTask α) :=
  fun ctx => do
    let childCtx ← ctx.fork
    Async.async (try x childCtx finally childCtx.cancel .cancel) prio

instance : MonadAsync AsyncTask ContextAsync where
  async x prio := ContextAsync.async x prio

instance : Functor ContextAsync where
  map f x := fun ctx => f <$> x ctx

instance : Monad ContextAsync where
  pure a := fun _ => pure a
  bind x f := fun ctx => x ctx >>= fun a => f a ctx

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

end ContextAsync

/--
Returns a selector that completes when the current context is cancelled.
This is useful for selecting on cancellation alongside other asynchronous operations.
-/
def Selector.cancelled : ContextAsync (Selector Unit) := do
  ContextAsync.doneSelector

end Async
end IO
end Internal
end Std
