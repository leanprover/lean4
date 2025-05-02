/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Sofia Rodrigues, Mac Malone
-/
prelude
import Init.Core
import Init.System.IO
import Init.System.Promise

namespace Std
namespace Internal
namespace IO
namespace Async

/-!
# Asynchronous Programming Primitives

This module provides a set of primitives for asynchronous programming:

## Task types

- `ExceptTask`: A task that may fail with an error.
- `AsyncTask`: A task that may fail with an `IO.Error` (alias for `ExceptTask IO.Error`)

## Momadic Interfaces

- `EAsync`: A monadic interface for working with asynchronous computations that may fail
- `Async`: A monadic interface for IO-based asynchronous computations (alias for `EAsync IO.Error`)
- `BaseAsync`: A monadic interface for infallible asynchronous computations (alias for `EAsync Empty`)

-/

/--
Represents monads that can suspend execution to await computations from another effect.
-/
class MonadAwait (n : Type → Type) (m : Type → Type) where
  /--
  Suspends execution until a computation from another effect completes.
  -/
  await : n α → m α

/--
Represents monads that can launch computations asynchronously in another effect.
-/
class MonadAsync (n : Type → Type) (m : Type → Type) where
  /--
  Starts an asynchronous computation in another monad.
  -/
  async : m α → m (n α)

/--
A `Task` that may resolve to either `α` value or an error value of type `ε`.
-/
def ExceptTask (ε : Type) (α : Type u) : Type u := Task (Except ε α)

namespace ExceptTask

/--
Create a new `ExceptTask` that will run after `x` has finished.

If `x`:
- errors, return an `ExceptTask` that resolves to the error.
- succeeds, return an `ExceptTask` that resolves to `f x`.
-/
@[inline]
protected def map (f : α → β) (x : ExceptTask ε α) : ExceptTask ε β :=
  Task.map (x := x) fun r =>
    match r with
    | .ok a => .ok (f a)
    | .error e => .error e

/--
Construct an `ExceptTask` that is already resolved with value `x`.
-/
@[inline]
protected def pure (x : α) : ExceptTask ε α :=
  Task.pure <| .ok x

/--
Creates a new `ExceptTask` that will run after `x` has completed.
-/
@[inline]
protected def bind (x : ExceptTask ε α) (f : α → ExceptTask ε β) : ExceptTask ε β :=
  Task.bind x fun r =>
    match r with
    | .ok a => f a
    | .error e => Task.pure <| .error e

/--
Similar to `bind`, however `f` has access to the `IO` monad. If `f` throws an error, the returned
`ExceptTask` resolves to that error.
-/
@[inline]
protected def bindIO (x : ExceptTask ε α) (f : α → EIO ε (ExceptTask ε β)) : EIO ε (ExceptTask ε β) :=
  EIO.bindTask x fun r =>
    match r with
    | .ok a => f a
    | .error e => .error e

/--
Similar to `bind`, however `f` has access to the `IO` monad. If `f` throws an error, the returned
`ExceptTask` resolves to that error.
-/
@[inline]
protected def mapIO (f : α → EIO ε β) (x : ExceptTask ε α) : BaseIO (ExceptTask ε β) :=
  EIO.mapTask (t := x) fun r =>
    match r with
    | .ok a => f a
    | .error e => .error e

/--
Block until the `ExceptTask` in `x` finishes.
-/
@[inline]
protected def block (x : ExceptTask ε α) : EIO ε α := do
  let res := x.get
  match res with
  | .ok a => return a
  | .error e => .error e

/--
Create an `ExceptTask` that resolves to the value of `x`.
-/
@[inline]
def ofPromise (x : IO.Promise (Except ε α)) : ExceptTask ε α :=
  x.result!

/--
Create an `ExceptTask` that resolves to the value of `x`.
-/
@[inline]
def ofPurePromise (x : IO.Promise α) : ExceptTask ε α :=
  x.result!.map pure

/--
Obtain the `IO.TaskState` of `x`.
-/
@[inline]
def getState (x : ExceptTask ε α) : BaseIO IO.TaskState :=
  IO.getTaskState x

instance : Functor (ExceptTask ε) where
  map := ExceptTask.map

instance : Monad (ExceptTask ε) where
  pure := ExceptTask.pure
  bind := ExceptTask.bind

end ExceptTask

/--
A `Task` that may resolve to a value or an error value of type `IO.Error`.
-/
abbrev AsyncTask := ExceptTask IO.Error

namespace AsyncTask

/--
Construct an `AsyncTask` that is already resolved with value `x`.
-/
@[inline]
protected def pure (x : α) : AsyncTask α :=
  Task.pure <| .ok x

/--
Create a new `AsyncTask` that will run after `x` has finished.
If `x`:
- errors, return an `AsyncTask` that resolves to the error.
- succeeds, run `f` on the result of `x` and return the `AsyncTask` produced by `f`.
-/
@[inline]
protected def bind (x : AsyncTask α) (f : α → AsyncTask β) : AsyncTask β :=
  Task.bind x fun r =>
    match r with
    | .ok a => f a
    | .error e => Task.pure <| .error e

/--
Create a new `AsyncTask` that will run after `x` has finished.
If `x`:
- errors, return an `AsyncTask` that resolves to the error.
- succeeds, return an `AsyncTask` that resolves to `f x`.
-/
@[inline]
def map (f : α → β) (x : AsyncTask α) : AsyncTask β :=
  Task.map (x := x) fun r =>
    match r with
    | .ok a => .ok (f a)
    | .error e => .error e

/--
Similar to `bind`, however `f` has access to the `IO` monad. If `f` throws an error, the returned
`AsyncTask` resolves to that error.
-/
@[inline]
def bindIO (x : AsyncTask α) (f : α → IO (AsyncTask β)) : IO (AsyncTask β) :=
  EIO.bindTask x fun r =>
    match r with
    | .ok a => f a
    | .error e => .error e

/--
Similar to `bind`, however `f` has access to the `IO` monad. If `f` throws an error, the returned
`AsyncTask` resolves to that error.
-/
@[inline]
def mapTaskIO (f : α → IO β) (x : AsyncTask α) : BaseIO (AsyncTask β) :=
  EIO.mapTask (t := x) fun r =>
    match r with
    | .ok a => f a
    | .error e => .error e

/--
Block until the `AsyncTask` in `x` finishes.
-/
def block (x : AsyncTask α) : IO α := do
  let res := x.get
  match res with
  | .ok a => return a
  | .error e => .error e

/--
Create an `AsyncTask` that resolves to the value of `x`.
-/
@[inline]
def ofPromise (x : IO.Promise (Except IO.Error α)) : AsyncTask α :=
  x.result!

/--
Create an `AsyncTask` that resolves to the value of `x`.
-/
@[inline]
def ofPurePromise (x : IO.Promise α) : AsyncTask α :=
  x.result!.map pure

/--
Obtain the `IO.TaskState` of `x`.
-/
@[inline]
def getState (x : AsyncTask α) : BaseIO IO.TaskState :=
  IO.getTaskState x

end AsyncTask

/--
A `MaybeExceptTask ε α` represents a computation that either:

- Is immediately available as an `α` value, or
- Is an asynchronous computation that will eventually produce an `α` value or an error `ε`
-/
inductive MaybeExceptTask (ε : Type) (α : Type)
  | pure : α → MaybeExceptTask ε α
  | ofTask : ExceptTask ε α → MaybeExceptTask ε α

namespace MaybeExceptTask

/--
Constructs an `ExceptTask` from a `MaybeExceptTask`.
-/
@[inline]
def toTask : MaybeExceptTask ε α → ExceptTask ε α
  | .pure a => .pure a
  | .ofTask t => t

/--
Gets the value of the `MaybeExceptTask` by blocking on the possible inside of it `ExceptTask`.
-/
@[inline]
def wait {α : Type} (x : MaybeExceptTask ε α) : EIO ε α :=
  match x with
  | .pure a => Pure.pure a
  | .ofTask t => t.block

/--
Join the `MaybeExceptTask` to an `ExceptTask`.
-/
@[inline]
def joinTask (t : ExceptTask ε (MaybeExceptTask ε α)) : ExceptTask ε α :=
  t.bind fun
    | .pure a => .pure a
    | .ofTask t => t

/--
Maps a function over a `MaybeExceptTask`.
-/
@[inline]
def map (f : α → β) (t : MaybeExceptTask ε α) : MaybeExceptTask ε β :=
  match t with
  | .pure a => .pure <| f a
  | .ofTask t => .ofTask <| t.map f

/--
Sequences two computations, allowing the second to depend on the value computed by the first.
-/
@[inline]
protected def bind (t : MaybeExceptTask ε α) (f : α → MaybeExceptTask ε β) : MaybeExceptTask ε β :=
  match t with
  | .pure a => f a
  | .ofTask t => .ofTask <| t.bind (f · |>.toTask)

instance : Functor (MaybeExceptTask ε) where
  map := MaybeExceptTask.map

instance : Monad (MaybeExceptTask ε) where
  pure := MaybeExceptTask.pure
  bind := MaybeExceptTask.bind

end MaybeExceptTask

/--
An asynchronous computation that may produce an error of type `ε`.
-/
structure EAsync (ε : Type) (α : Type) where
  toRawEIO : EIO ε (Async.MaybeExceptTask ε α)

namespace EAsync

/--
Lifts an `EAsync` computation into an `ExceptTask` that can be awaited and joined.
-/
@[inline]
protected def asTask (x : EAsync ε α) : EIO ε (ExceptTask ε α) := do
  let res ← x.toRawEIO
  pure res.toTask

/--
Binds a `MaybeExceptTask` using a function that returns an `EAsync`.
-/
@[inline]
def bindAsyncTask (t : MaybeExceptTask ε α) (f : α → EAsync ε β) : EAsync ε β := .mk <|
  match t with
  | .pure a => f a |>.toRawEIO
  | .ofTask t => .ofTask <$> t.bindIO (fun s => MaybeExceptTask.toTask <$> (f s |>.toRawEIO))

/--
Creates an `EAsync` computation that immediately returns the given value.
-/
@[inline]
protected def pure (a : α) : EAsync ε α :=
  .mk <| pure <| .pure a

/--
Lifts a `EIO` action into an `EAsync` computation.
-/
@[inline]
protected def lift (x : EIO ε α) : EAsync ε α :=
  .mk <| (.pure ∘ .pure) =<< x

/--
Maps the result of an `EAsync` computation with a pure function.
-/
@[inline]
protected def map (f : α → β) (self : EAsync ε α) : EAsync ε β :=
  mk <| (·.map f) <$> self.toRawEIO

/--
Waits for the result of the `EAsync` computation, blocking if necessary.
-/
@[inline]
protected def wait (self : EAsync ε α) : EIO ε α :=
  self.toRawEIO >>= MaybeExceptTask.wait

/--
Sequences two computations, allowing the second to depend on the value computed by the first.
-/
@[inline]
protected def bind (self : EAsync ε α) (f : α → EAsync ε β) : EAsync ε β :=
  mk <| self.toRawEIO >>= (bindAsyncTask · f |>.toRawEIO)

/--
Raises an `IO.Error` within the `EAsync` monad.
-/
@[inline]
protected def throw (e : ε) : EAsync ε α :=
  ⟨throw e⟩

/--
Handles errors in an `EAsync` computation by running a handler if one occurs.
-/
@[inline]
protected def tryCatch (x : EAsync ε α) (f : ε → EAsync ε α) : EAsync ε α :=
  .mk fun w =>
    match x.toRawEIO w with
    | .ok (.pure a) s => .ok (.pure a) s
    | .ok (.ofTask t) s => .ok (.ofTask (Task.bind t (catcher f s))) s
    | .error a s => .error a s
  where
    catcher {α} (f : ε → EAsync ε α) (s : IO.RealWorld) : Except ε α → Task (Except ε α)
      | .ok res => Task.pure (.ok res)
      | .error res =>
        match f res |>.toRawEIO s with
        | .ok (.pure a) _ => Task.pure (.ok a)
        | .ok (.ofTask t) _ => t
        | .error a _ => Task.pure (.error a)

/--
Runs an action, ensuring that some other action always happens afterward.
-/
protected def tryFinally' (x : EAsync ε α) (f : Option α → EAsync ε β) : EAsync ε (α × β) :=
  .mk <| fun w =>
    match x.toRawEIO w with
    | .ok (.pure a) s => match f (some a) |>.toRawEIO s with
      | .ok (.pure b) s => .ok (.pure (a, b)) s
      | .ok (.ofTask b) s => .ok (.ofTask <| b.map (a, ·)) s
      | .error e s => .error e s
    | .ok (.ofTask a) s => .ok (.ofTask <| a.bind fun a => match f (some a) |>.toRawEIO s with
      | .ok (.pure b) _ => ExceptTask.pure (a, b)
      | .ok (.ofTask b) _ => b.map (a, ·)
      | .error e _ => Task.pure (.error e)
      ) s
    | .error a s => match f none |>.toRawEIO s with
      | .ok (.pure _) s => .error a s
      | .ok (.ofTask b) s => .ok (.ofTask <| Task.map (fun
        | .ok _ => .error a
        | .error b => .error b) b) s
      | .error e s => .error e s

/--
Returns the `EAsync` computation inside a the `ExceptTask ε α`, so it can be awaited.
-/
@[inline]
def async (self : EAsync ε α) : EAsync ε (ExceptTask ε α) :=
  EAsync.lift <| self.asTask

/--
Creates an `EAsync` computation that awaits the completion of the given `ExceptTask ε α`.
-/
@[inline]
def await (x : ExceptTask ε α) : EAsync ε α :=
  EAsync.mk (pure <| MaybeExceptTask.ofTask x)

@[default_instance]
instance : MonadAwait (ExceptTask ε) (EAsync ε) where
  await t := mk <| pure <| .ofTask t

instance : MonadAwait AsyncTask (EAsync IO.Error) where
  await t := mk <| pure <| .ofTask t

instance : MonadAwait IO.Promise (EAsync ε) where
  await t := mk <| pure <| .ofTask (t.result!.map (.ok))

@[default_instance]
instance : MonadAsync (ExceptTask ε) (EAsync ε) where
  async t := EAsync.lift <| t.asTask

instance : MonadAsync AsyncTask (EAsync IO.Error) where
  async t := EAsync.lift <| t.asTask

instance : Functor (EAsync ε) where
  map := EAsync.map

instance : Monad (EAsync ε) where
  pure := EAsync.pure
  bind := EAsync.bind

instance : MonadLift (EIO ε) (EAsync ε) where
  monadLift := EAsync.lift

instance : MonadExcept ε (EAsync ε) where
  throw := EAsync.throw
  tryCatch := EAsync.tryCatch

instance : MonadExceptOf ε (EAsync ε) where
  throw := EAsync.throw
  tryCatch := EAsync.tryCatch

instance : MonadFinally (EAsync ε) where
  tryFinally' := EAsync.tryFinally'

instance : OrElse (EAsync ε α) where
  orElse := MonadExcept.orElse

instance [Inhabited ε] : Inhabited (EAsync ε α) where
  default := ⟨.error default⟩

/--
Starts the given `ExceptTask` in the background and discards the result.
-/
@[inline]
def parallel {α : Type} (x : EAsync ε (ExceptTask ε α)) : EAsync ε Unit :=
  discard <| x

end EAsync

/--
An asynchronous computation that may produce an error of type `IO.Error`.
-/
abbrev Async (α : Type) := EAsync IO.Error α

namespace Async

/--
Waits for the result of the `Async` computation, blocking if necessary.
-/
@[inline]
protected def wait (self : Async α) : IO α :=
  self.toRawEIO >>= MaybeExceptTask.wait

/--
Lifts an `Async` computation into an `AsyncTask` that can be awaited and joined.
-/
@[inline]
def asTask (x : Async α) : IO (AsyncTask α) := do
  MaybeExceptTask.joinTask <$> IO.asTask x.toRawEIO


/--
Returns the `Async` computation inside a the `AsyncTask`, so it can be awaited.
-/
@[inline]
def async (self : Async α) : Async (AsyncTask α) :=
  EAsync.lift <| self.asTask

@[default_instance] instance : MonadAwait AsyncTask Async := inferInstanceAs (MonadAwait AsyncTask (EAsync IO.Error))
@[default_instance] instance : MonadAsync AsyncTask Async := inferInstanceAs (MonadAsync (ExceptTask IO.Error) (EAsync IO.Error))
instance : MonadAwait IO.Promise Async := inferInstanceAs (MonadAwait IO.Promise (EAsync IO.Error))

end Async

/--
An asynchronous computation that cannot fail with any error.
-/
abbrev BaseAsync (α : Type) := EAsync Empty α

namespace BaseAsync

/--
Waits for the result of the `BaseAsync` computation, blocking if necessary.
-/
@[inline]
protected def wait (self : BaseAsync α) : BaseIO α :=
  self.toRawEIO >>= MaybeExceptTask.wait

/--
Lifts an `Async` computation into an `AsyncTask` that can be awaited and joined.
-/
@[inline]
def asTask (x : BaseAsync α) : EIO ε (Task α) := do
  let task ← MaybeExceptTask.joinTask <$> EIO.asTask x.toRawEIO
  return Task.map (prio := 0) (fun (.ok r) => r) task

/--
Creates a `BaseAsync` that awaits the completion of the given `Task α`.
-/
@[inline]
def await (t : Task α) : BaseAsync α :=
  .mk <| pure <| .ofTask <| t.map (fun x => .ok x)

/--
Returns the `EAsync` computation insside a the `AsyncTask α`, so it can be awaited.
-/
@[inline]
def async (self : BaseAsync α) : BaseAsync (Task α) :=
  EAsync.lift <| self.asTask

instance : MonadAwait (ExceptTask Empty) BaseAsync :=
  inferInstanceAs (MonadAwait (ExceptTask Empty) (EAsync Empty))

@[default_instance]
instance : MonadAwait Task BaseAsync where
  await := BaseAsync.await

@[default_instance]
instance : MonadAsync Task BaseAsync where
  async := BaseAsync.async

end BaseAsync

export MonadAsync (async)
export MonadAwait (await)
export EAsync (parallel)

end Async
end IO
end Internal
end Std
