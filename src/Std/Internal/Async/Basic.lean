/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Sofia Rodrigues, Mac Malone
-/
module

prelude
public import Init.System.Promise

public section

namespace Std
namespace Internal
namespace IO
namespace Async

/-!

# Asynchronous Programming Primitives

This module provides a layered approach to asynchronous programming, combining monadic types,
type classes, and concrete task types that work together in a cohesive system.

- **Monadic Types**: These types provide a good way to chain and manipulate context. These
  can contain a `Task`, enabling manipulation of both asynchronous and synchronous code.
- **Concrete Task Types**: Concrete units of work that can be executed within these contexts.

## Monadic Types

These types provide a good way to chain and manipulate context. These can contain a `Task`,
enabling manipulation of both asynchronous and synchronous code.

- `BaseAsync`: A monadic type for infallible asynchronous computations
- `EAsync`: A monadic type for asynchronous computations that may fail with an error of type
  `ε`
- `Async`: A monadic type for IO-based asynchronous computations that may fail with `IO.Error`
  (alias for `EAsync IO.Error`)

## Concurrent Units of Work

These are the concrete computational units that exist within the monadic contexts. These types
should not be created directly.

- `Task`: A computation that will resolve to a value of type `α`,
- `ETask`: A task that may fail with an error of type `ε`.
- `AsyncTask`: A task that may fail with an `IO.Error` (alias for `ETask IO.Error`).

## Relation

These types are related by two functions in the type classes `MonadAsync` and `MonadAwait`: `async`
and `await`. The `async` function extracts a concrete asynchronous task from a computation within the
monadic context. In effect, it runs the computation in the background and returns a task handle that
can be awaited later. On the other hand, the `await` function takes a task and re-inserts it into the
monadic context, allowing its result to be composed using monadic bind and also pausing to wait for that result.
This relationship between `async` and `await` enables precise control over when a computation begins
and when its result is used. You can spawn multiple asynchronous tasks using `async`, perform other
operations in the meantime, and later rejoin the computation flow by awaiting their results.

These functions should not be used directly. Instead, prefer higher-level combinators such as
`race`, `raceAll`, `concurrently`, `background` and `concurrentlyAll`. The best way to think about
how to write your async code, it to avoid using the concurrent units of work, and only use it when integrating
with non async code that uses them.

-/

/--
Typeclass for monads that can "await" a computation of type `t α` in a monad `m` until the result is
available.
-/
class MonadAwait (t : Type → Type) (m : Type → Type) where
  /--
  Awaits the result of `t α` and returns it inside the `m` monad.
  -/
  await : t α → m α

/--
Represents monads that can launch computations asynchronously of type `t` in a monad `m`.
-/
class MonadAsync (t : Type → Type) (m : Type → Type) where
  /--
  Starts an asynchronous computation in another monad.
  -/
  async (x : m α) (prio := Task.Priority.default) : m (t α)

/-
These instances have the default_instance attribute so that other default instances
can function correctly within monad transformers.
-/

@[default_instance]
instance [Monad m] [MonadAwait t m] : MonadAwait t (StateT n m) where
  await := liftM (m := m) ∘ MonadAwait.await

@[default_instance]
instance [Monad m] [MonadAwait t m] : MonadAwait t (ExceptT n m) where
  await := liftM (m := m) ∘ MonadAwait.await

@[default_instance]
instance [Monad m] [MonadAwait t m] : MonadAwait t (ReaderT n m) where
  await := liftM (m := m) ∘ MonadAwait.await

@[default_instance]
instance [MonadAwait t m] : MonadAwait t (StateRefT' s n m) where
  await := liftM (m := m) ∘ MonadAwait.await

@[default_instance]
instance [Monad m] [MonadAwait t m] : MonadAwait t (StateT s m) where
  await := liftM (m := m) ∘ MonadAwait.await

@[default_instance]
instance [MonadAsync t m] : MonadAsync t (ReaderT n m) where
  async p prio := MonadAsync.async (prio := prio) ∘ p

@[default_instance]
instance [MonadAsync t m] : MonadAsync t (StateRefT' s n m) where
  async p prio := MonadAsync.async (prio := prio) ∘ p

@[default_instance]
instance [Monad m] [Functor t] [inst : MonadAsync t m] : MonadAsync t (StateT s m) where
  async p prio := fun s => do
    let t ← inst.async (prio := prio) (p s)
    pure (t <&> Prod.fst, s)

/--
A `Task` that may resolve to either a value of type `α` or an error value of type `ε`.
-/
abbrev ETask (ε : Type) (α : Type) : Type := ExceptT ε Task α

namespace ETask

/--
Construct an `ETask` that is already resolved with value `x`.
-/
@[inline]
protected def pure (x : α) : ETask ε α :=
  Task.pure <| .ok x

/--
Creates a new `ETask` that will run after `x` has finished. If `x`:
- errors, return an `ETask` that resolves to the error.
- succeeds, return an `ETask` that resolves to `f x`.
-/
@[inline]
protected def map (f : α → β) (x : ETask ε α) (prio := Task.Priority.default) (sync := false) : ETask ε β :=
  Task.map (x := x) (f <$> ·) prio sync

/--
Creates a new `ETask` that will run after `x` has completed. If `x`:
- errors, return an `ETask` that resolves to the error.
- succeeds, run `f` on the result of `x` and return the `ETask` produced by `f`.
-/
@[inline]
protected def bind (x : ETask ε α) (f : α → ETask ε β) (prio := Task.Priority.default) (sync := false) : ETask ε β :=
  Task.bind x (prio := prio) (sync := sync) fun
    | .ok a => f a
    | .error e => Task.pure <| .error e

/--
Similar to `bind`, however `f` has access to the `EIO` monad. If `f` throws an error, the returned
`ETask` resolves to that error.
-/
@[inline]
protected def bindEIO (x : ETask ε α) (f : α → EIO ε (ETask ε β)) (prio := Task.Priority.default) (sync := false) : EIO ε (ETask ε β) :=
  EIO.bindTask x (prio := prio) (sync := sync) fun
    | .ok a => f a
    | .error e => throw e

/--
Similar to `bind`, however `f` has access to the `EIO` monad. If `f` throws an error, the returned
`ETask` resolves to that error.
-/
@[inline]
protected def mapEIO (f : α → EIO ε β) (x : ETask ε α) (prio := Task.Priority.default) (sync := false) : BaseIO (ETask ε β) :=
  EIO.mapTask (t := x) (prio := prio) (sync := sync) fun
    | .ok a => f a
    | .error e => throw e

/--
Block until the `ETask` in `x` finishes and returns its value. Propagates any error encountered
during execution.
-/
@[inline]
def block (x : ETask ε α) : EIO ε α := do
  match x.get with
  | .ok a => return a
  | .error e => throw e

/--
Create an `ETask` that resolves to the value of the promise `x`. If the promise gets dropped then it
panics.
-/
@[inline]
def ofPromise! (x : IO.Promise (Except ε α)) : ETask ε α :=
  x.result!

/--
Create an `ETask` that resolves to the pure value of the promise `x`. If the promise gets dropped then it
panics.
-/
@[inline]
def ofPurePromise (x : IO.Promise α) : ETask ε α :=
  x.result!.map pure (sync := true)

/--
Obtain the `IO.TaskState` of `x`.
-/
@[inline]
def getState (x : ETask ε α) : BaseIO IO.TaskState :=
  IO.getTaskState x

instance : Functor (ETask ε) where
  map := ETask.map

instance : Monad (ETask ε) where
  pure := ETask.pure
  bind := ETask.bind

end ETask

/--
A `Task` that may resolve to a value or an error value of type `IO.Error`. Alias for `ETask IO.Error`.
-/
abbrev AsyncTask := ETask IO.Error

namespace AsyncTask

/--
Similar to `map`, however `f` has access to the `IO` monad. If `f` throws an error, the returned
`AsyncTask` resolves to that error.
-/
@[inline]
protected def mapIO (f : α → IO β) (x : AsyncTask α) (prio := Task.Priority.default) (sync := false) : BaseIO (AsyncTask β) :=
  EIO.mapTask (t := x) (prio := prio) (sync := sync) fun
    | .ok a => f a
    | .error e => throw e

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
protected def bind (x : AsyncTask α) (f : α → AsyncTask β) (prio := Task.Priority.default) (sync := false) : AsyncTask β :=
  Task.bind x (prio := prio) (sync := sync) fun
    | .ok a => f a
    | .error e => Task.pure <| .error e

/--
Create a new `AsyncTask` that will run after `x` has finished.
If `x`:
- errors, return an `AsyncTask` that resolves to the error.
- succeeds, return an `AsyncTask` that resolves to `f x`.
-/
@[inline]
def map (f : α → β) (x : AsyncTask α) (prio := Task.Priority.default) (sync := false) : AsyncTask β :=
  Task.map (x := x) (f <$> ·) prio sync

/--
Similar to `bind`, however `f` has access to the `IO` monad. If `f` throws an error, the returned
`AsyncTask` resolves to that error.
-/
@[inline]
def bindIO (x : AsyncTask α) (f : α → IO (AsyncTask β)) (prio := Task.Priority.default) (sync := false) : BaseIO (AsyncTask β) :=
  IO.bindTask x (prio := prio) (sync := sync) fun
    | .ok a => f a
    | .error e => throw e

/--
Similar to `map`, however `f` has access to the `IO` monad. If `f` throws an error, the returned
`AsyncTask` resolves to that error.
-/
@[inline]
def mapTaskIO (f : α → IO β) (x : AsyncTask α) (prio := Task.Priority.default) (sync := false) : BaseIO (AsyncTask β) :=
  IO.mapTask (t := x) (prio := prio) (sync := sync) fun
    | .ok a => f a
    | .error e => throw e

/--
Block until the `AsyncTask` in `x` finishes.
-/
def block (x : AsyncTask α) : IO α :=
  match x.get with
  | .ok a => return a
  | .error e => throw e

/--
Create an `AsyncTask` that resolves to the value of `x`.
-/
@[inline]
def ofPromise (x : IO.Promise (Except IO.Error α)) (error : String := "the promise linked to the Async Task was dropped") : AsyncTask α :=
  x.result?.map fun
    | none => .error error
    | some res => res

/--
Create an `AsyncTask` that resolves to the value of `x`.
-/
@[inline]
def ofPurePromise (x : IO.Promise α) (error : String := "the promise linked to the Async Task was dropped") : AsyncTask α :=
  x.result?.map (sync := true) fun
    | none => .error error
    | some res => pure res

/--
Obtain the `IO.TaskState` of `x`.
-/
@[inline]
def getState (x : AsyncTask α) : BaseIO IO.TaskState :=
  IO.getTaskState x

end AsyncTask

/--
A `MaybeTask α` represents a computation that either:

- Is immediately available as an `α` value, or
- Is an asynchronous computation that will eventually produce an `α` value.
-/
inductive MaybeTask (α : Type)
  | pure : α → MaybeTask α
  | ofTask : Task α → MaybeTask α

namespace MaybeTask

/--
Constructs an `Task` from a `MaybeTask`.
-/
@[inline]
def toTask : MaybeTask α → Task α
  | .pure a => .pure a
  | .ofTask t => t

/--
Gets the value of the `MaybeTask` by blocking.
-/
@[inline]
def get {α : Type} : MaybeTask α → α
  | .pure a => a
  | .ofTask t => t.get

/--
Maps a function over a `MaybeTask`.
-/
@[inline]
def map (f : α → β) (prio := Task.Priority.default) (sync := false) : MaybeTask α → MaybeTask β
  | .pure a => .pure <| f a
  | .ofTask t => .ofTask <| t.map f prio sync

/--
Sequences two computations, allowing the second to depend on the value computed by the first.
-/
@[inline]
protected def bind (t : MaybeTask α) (f : α → MaybeTask β) (prio := Task.Priority.default) (sync := false) : MaybeTask β :=
  match t with
  | .pure a => f a
  | .ofTask t => .ofTask <| t.bind (f · |>.toTask) prio sync

/--
Join the `MaybeTask` to an `Task`.
-/
@[inline]
def joinTask (t : Task (MaybeTask α)) : Task α :=
  t.bind (sync := true) fun
    | .pure a => .pure a
    | .ofTask t => t

instance : Functor MaybeTask where
  map := MaybeTask.map

instance : Monad MaybeTask where
  pure := MaybeTask.pure
  bind := MaybeTask.bind

end MaybeTask

/--
An asynchronous computation that never fails.
-/
@[expose] def BaseAsync (α : Type) := BaseIO (MaybeTask α)

namespace BaseAsync

/--
Converts a `BaseIO` into a `BaseAsync`
-/
@[inline]
def mk (x : BaseIO (MaybeTask α)) : BaseAsync α :=
  x

/--
Converts a `BaseAsync` into a `BaseIO`
-/
@[inline]
def toRawBaseIO (x : BaseAsync α) : BaseIO (MaybeTask α) :=
  x

/--
Converts a `BaseAsync` to a `BaseIO Task`.
-/
@[inline]
protected def toBaseIO (x : BaseAsync α) : BaseIO (Task α) :=
  MaybeTask.toTask <$> x.toRawBaseIO

/--
Creates a new `BaseAsync` out of a `Task`.
-/
@[inline]
protected def ofTask (x : Task α) : BaseAsync α :=
  .mk <| pure <| MaybeTask.ofTask x

/--
Creates a `BaseAsync` computation that immediately returns the given value.
-/
@[inline]
protected def pure (a : α) : BaseAsync α :=
  .mk <| pure <| .pure a

/--
Maps the result of a `BaseAsync` computation with a function.
-/
@[inline]
protected def map (f : α → β) (self : BaseAsync α) (prio := Task.Priority.default) (sync := false) : BaseAsync β :=
  mk <| (·.map f prio sync) <$> self.toRawBaseIO

/--
Sequences two computations, allowing the second to depend on the value computed by the first.
-/
@[inline]
protected def bind (self : BaseAsync α) (f : α → BaseAsync β) (prio := Task.Priority.default) (sync := false) : BaseAsync β :=
  mk <| self.toRawBaseIO >>= (bindAsyncTask · f |>.toRawBaseIO)
where
  bindAsyncTask (t : MaybeTask α) (f : α → BaseAsync β) : BaseAsync β := .mk <|
    match t with
    | .pure a => (f a) |>.toRawBaseIO
    | .ofTask t => .ofTask <$> BaseIO.bindTask t (fun a => MaybeTask.toTask <$> (f a |>.toRawBaseIO)) prio sync

/--
Lifts a `BaseIO` action into a `BaseAsync` computation.
-/
@[inline]
protected def lift (x : BaseIO α) : BaseAsync α :=
  .mk <| (pure ∘ pure) =<< x

/--
Waits for the result of the `BaseAsync` computation, blocking if necessary.
-/
@[inline]
protected def wait (self : BaseAsync α) : BaseIO α :=
  pure ∘ Task.get =<< self.toBaseIO

/--
Lifts a `BaseAsync` computation into a `Task` that can be awaited and joined.
-/
@[inline]
protected def asTask (x : BaseAsync α) (prio := Task.Priority.default) : BaseIO (Task α) := do
  let res ← BaseIO.asTask (prio := prio) x.toRawBaseIO
  return MaybeTask.joinTask res

/--
Creates a `BaseAsync` that awaits the completion of the given `Task α`.
-/
@[inline]
def await (t : Task α) : BaseAsync α :=
  .mk <| pure <| MaybeTask.ofTask t

/--
Returns the `BaseAsync` computation inside a `Task α`, so it can be awaited.
-/
@[inline]
def async (self : BaseAsync α) (prio := Task.Priority.default) : BaseAsync (Task α) :=
  BaseAsync.lift <| self.asTask (prio := prio)

instance : Functor BaseAsync where
  map := BaseAsync.map

instance : Monad BaseAsync where
  pure := BaseAsync.pure
  bind := BaseAsync.bind

instance : MonadLift BaseIO BaseAsync where
  monadLift := BaseAsync.lift

instance : MonadAwait Task BaseAsync where
  await := BaseAsync.await

instance : MonadAsync Task BaseAsync where
  async t prio := BaseAsync.async t prio

instance [Inhabited α] : Inhabited (BaseAsync α) where
  default := .mk <| pure (MaybeTask.pure default)

instance : MonadFinally BaseAsync where
  tryFinally' x f := do
    let res ← x
    Prod.mk res <$> f (some res)

/--
Converts `Except` to `BaseAsync`.
-/
@[inline]
protected def ofExcept (except : Except Empty α) : BaseAsync α :=
  pure (f := BaseIO) <| MaybeTask.pure <| match except with | .ok res => res

/--
Runs two computations concurrently and returns both results as a pair.
-/
@[inline, specialize]
def concurrently (x : BaseAsync α) (y : BaseAsync β) (prio := Task.Priority.default) : BaseAsync (α × β) := do
  let taskX : Task _ ← MonadAsync.async x (prio := prio)
  let taskY : Task _ ← MonadAsync.async y (prio := prio)
  let resultX ← MonadAwait.await taskX
  let resultY ← MonadAwait.await taskY
  return (resultX, resultY)

/--
Runs two computations concurrently and returns the result of the one that finishes first.
The other result is lost and the other task is not cancelled, so the task will continue the execution
until the end.
-/
@[inline, specialize]
def race [Inhabited α] (x : BaseAsync α) (y : BaseAsync α) (prio := Task.Priority.default) : BaseAsync α := do
  let promise ← IO.Promise.new

  let task₁ : Task _ ← MonadAsync.async (prio := prio) x
  let task₂ : Task _ ← MonadAsync.async (prio := prio) y

  BaseIO.chainTask task₁ (liftM ∘ promise.resolve)
  BaseIO.chainTask task₂ (liftM ∘ promise.resolve)

  MonadAwait.await promise.result!

/--
Runs all computations in an `Array` concurrently and returns all results as an array.
-/
@[inline, specialize]
def concurrentlyAll (xs : Array (BaseAsync α)) (prio := Task.Priority.default) :  BaseAsync (Array α) := do
  let tasks : Array (Task α) ← xs.mapM (MonadAsync.async (prio := prio))
  tasks.mapM MonadAwait.await

/--
Runs all computations concurrently and returns the result of the first one to finish.
All other results are lost, and the tasks are not cancelled, so they'll continue their execution
until the end.
-/
@[inline, specialize]
def raceAll [Inhabited α] [ForM BaseAsync c (BaseAsync α)] (xs : c) (prio := Task.Priority.default) : BaseAsync α := do
  let promise ← IO.Promise.new

  ForM.forM xs fun x => do
    let task₁ ← MonadAsync.async (t := Task) (prio := prio) x
    BaseIO.chainTask task₁ (liftM ∘ promise.resolve)

  MonadAwait.await promise.result!

end BaseAsync

/--
An asynchronous computation that may produce an error of type `ε`.
-/
@[expose] def EAsync (ε : Type) (α : Type) := BaseAsync (Except ε α)

namespace EAsync

/--
Converts a `EAsync` to a `ETask`.
-/
@[inline]
protected def toBaseIO (x : EAsync ε α) : BaseIO (ETask ε α) :=
  MaybeTask.toTask <$> x.toRawBaseIO

/--
Creates a new `EAsync` out of a `RTask`.
-/
@[inline]
protected def ofTask (x : ETask ε α) : EAsync ε α :=
  .mk <| pure <| MaybeTask.ofTask x

/--
Converts a `BaseAsync` to a `EIO ETask`.
-/
@[inline]
protected def toEIO (x : EAsync ε α) : EIO ε (ETask ε α) :=
  MaybeTask.toTask <$> x.toRawBaseIO

/--
Creates a new `EAsync` out of a `ETask`.
-/
@[inline]
protected def ofETask (x : ETask ε α) : EAsync ε α :=
  .mk <| BaseAsync.ofTask x

/--
Creates an `EAsync` computation that immediately returns the given value.
-/
@[inline]
protected def pure (a : α) : EAsync ε α :=
  .mk <| BaseAsync.pure <| .ok a

/--
Maps the result of an `EAsync` computation with a pure function.
-/
@[inline]
protected def map (f : α → β) (self : EAsync ε α) : EAsync ε β :=
  .mk <| BaseAsync.map (.map f) self

/--
Sequences two computations, allowing the second to depend on the value computed by the first.
-/
@[inline]
protected def bind (self : EAsync ε α) (f : α → EAsync ε β) : EAsync ε β :=
  .mk <| BaseAsync.bind self fun
    | .ok a => f a
    | .error e => BaseAsync.pure (.error e)

/--
Lifts an `EIO` action into an `EAsync` computation.
-/
@[inline]
protected def lift (x : EIO ε α) : EAsync ε α :=
  .mk <| BaseAsync.lift x.toBaseIO

/--
Waits for the result of the `EAsync` computation, blocking if necessary.
-/
@[inline]
protected def wait (self : EAsync ε α) : EIO ε α := do
  let result ← self |> BaseAsync.wait
  match result with
  | .ok a => return a
  | .error e => throw e

/--
Lifts an `EAsync` computation into an `ETask` that can be awaited and joined.
-/
@[inline]
protected def asTask (x : EAsync ε α) (prio := Task.Priority.default) : EIO ε (ETask ε α) :=
  x |> BaseAsync.asTask (prio := prio)

/--
Block until the `EAsync` finishes and returns its value. Propagates any error encountered during execution.
-/
@[inline]
protected def block (x : EAsync ε α) (prio := Task.Priority.default) : EIO ε α :=
  x.asTask (prio := prio) >>= ETask.block

/--
Raises an error of type `ε` within the `EAsync` monad.
-/
@[inline]
protected def throw (e : ε) : EAsync ε α :=
  .mk <| BaseAsync.pure (.error e)

/--
Handles errors in an `EAsync` computation by running a handler if one occurs.
-/
@[inline]
protected def tryCatch (x : EAsync ε α) (f : ε → EAsync ε α) (prio := Task.Priority.default) (sync := false) : EAsync ε α :=
  .mk <| BaseAsync.bind (sync := sync) (prio := prio) x fun
    | .ok a => BaseAsync.pure (.ok a)
    | .error e => (f e)

/--
Runs an action, ensuring that some other action always happens afterward.
-/
protected def tryFinally'
    (x : EAsync ε α) (f : Option α → EAsync ε β)
    (prio := Task.Priority.default) (sync := false) :
    EAsync ε (α × β) :=
  .mk <| BaseAsync.bind x (prio := prio) (sync := sync) fun
    | .ok a => do
      match ← (f (some a)) with
      | .ok b => BaseAsync.pure (.ok (a, b))
      | .error e => BaseAsync.pure (.error e)
    | .error e => do
      match ← (f none) with
      | .ok _ => BaseAsync.pure (.error e)
      | .error e' => BaseAsync.pure (.error e')

/--
Creates an `EAsync` computation that awaits the completion of the given `ETask ε α`.
-/
@[inline]
def await (x : ETask ε α) : EAsync ε α :=
  .mk (BaseAsync.ofTask x)

/--
Returns the `EAsync` computation inside an `ETask ε α`, so it can be awaited.
-/
@[inline]
def async (self : EAsync ε α) (prio := Task.Priority.default) : EAsync ε (ETask ε α) :=
  EAsync.lift <| self.asTask prio

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
  default := .mk <| BaseAsync.pure default

instance : MonadAwait (ETask ε) (EAsync ε) where
  await t := .mk <| BaseAsync.ofTask t

instance : MonadAwait Task (EAsync ε) where
  await t := .mk <| BaseAsync.ofTask (t.map (.ok))

instance : MonadAwait AsyncTask (EAsync IO.Error) where
  await t := .mk <| BaseAsync.ofTask t

instance : MonadAwait IO.Promise (EAsync ε) where
  await t := .mk <| BaseAsync.ofTask (t.result!.map (.ok))

instance : MonadAsync (ETask ε) (EAsync ε) where
  async t prio := EAsync.lift <| t.asTask (prio := prio)

instance : MonadAsync AsyncTask (EAsync IO.Error) where
  async t prio := EAsync.lift <| t.asTask (prio := prio)

instance : MonadLift BaseIO (EAsync ε) where
  monadLift x := .mk <| (pure ∘ .ok) <$> x

instance : MonadLift (EIO ε) (EAsync ε) where
  monadLift x := .mk <| pure <$> x.toBaseIO

instance : MonadLift BaseAsync (EAsync ε) where
  monadLift x := .mk <| x.map (.ok)

@[inline]
protected partial def forIn
    {β : Type} (init : β)
    (f : Unit → β → EAsync ε (ForInStep β))
    (prio := Task.Priority.default) :
    EAsync ε β := do

  have : Nonempty β := ⟨init⟩
  let promise ← IO.Promise.new

  let rec @[specialize] loop (b : β) : BaseIO Unit := do
    match ← f () b with
    | MaybeTask.pure result =>
      match result with
      | .error e => promise.resolve (.error e)
      | .ok (.done b) => promise.resolve (.ok b)
      | .ok (.yield b) => loop b
    | MaybeTask.ofTask task => BaseIO.chainTask (prio := prio) task fun
      | .error e => promise.resolve (.error e)
      | .ok (.done b) => promise.resolve (.ok b)
      | .ok (.yield b) => loop b

  loop init
  .mk <| EAsync.ofETask promise.result!

instance : ForIn (EAsync ε) Lean.Loop Unit where
  forIn _ := EAsync.forIn

/--
Converts `Except` to `EAsync`.
-/
@[inline]
protected def ofExcept (except : Except ε α) : EAsync ε α :=
  pure (f := BaseIO) (MaybeTask.pure except)

/--
Runs two computations concurrently and returns both results as a pair.
-/
@[inline, specialize]
def concurrently (x : EAsync ε α) (y : EAsync ε β) (prio := Task.Priority.default) : EAsync ε (α × β) := do
  let taskX : ETask ε _ ← MonadAsync.async x (prio := prio)
  let taskY : ETask ε _ ← MonadAsync.async y (prio := prio)
  let resultX ← MonadAwait.await taskX
  let resultY ← MonadAwait.await taskY
  return (resultX, resultY)

/--
Runs two computations concurrently and returns the result of the one that finishes first.
The other result is lost and the other task is not cancelled, so the task will continue the execution
until the end.
-/
@[inline, specialize]
def race [Inhabited α] (x : EAsync ε α) (y : EAsync ε α)
    (prio := Task.Priority.default) :
    EAsync ε α := do
  let promise ← IO.Promise.new

  let task₁ : ETask ε _ ← MonadAsync.async (prio := prio) x
  let task₂ : ETask ε _ ← MonadAsync.async (prio := prio) y

  BaseIO.chainTask task₁ (liftM ∘ promise.resolve)
  BaseIO.chainTask task₂ (liftM ∘ promise.resolve)

  let result ← MonadAwait.await promise.result!
  EAsync.ofExcept result

/--
Runs all computations in an `Array` concurrently and returns all results as an array.
-/
@[inline, specialize]
def concurrentlyAll (xs : Array (EAsync ε α)) (prio := Task.Priority.default) : EAsync ε (Array α) := do
  let tasks : Array (ETask ε α) ← xs.mapM (MonadAsync.async (prio := prio))
  tasks.mapM MonadAwait.await

/--
Runs all computations concurrently and returns the result of the first one to finish.
All other results are lost, and the tasks are not cancelled, so they'll continue their execution
until the end.
-/
@[inline, specialize]
def raceAll [Inhabited α] [ForM (EAsync ε) c (EAsync ε α)] (xs : c) (prio := Task.Priority.default) : EAsync ε α := do
  let promise ← IO.Promise.new

  ForM.forM xs fun x => do
    let task₁ ← MonadAsync.async (t := ETask ε) (prio := prio) x
    BaseIO.chainTask task₁ (liftM ∘ promise.resolve)

  let result ← MonadAwait.await promise.result!
  EAsync.ofExcept result

end EAsync

/--
An asynchronous computation that may produce an error of type `IO.Error`..
-/
abbrev Async (α : Type) := EAsync IO.Error α

namespace Async

/--
Converts a `Async` to a `AsyncTask`.
-/
@[inline]
protected def toIO (x : Async α) : IO (AsyncTask α) :=
  MaybeTask.toTask <$> x.toRawBaseIO

/--
Block until the `Async` finishes and returns its value. Propagates any error encountered during execution.
-/
@[inline]
protected def block (x : Async α) (prio := Task.Priority.default) : IO α :=
  x.asTask (prio := prio) >>= ETask.block

/--
Converts `Promise` into `Async`.
-/
@[inline]
protected def ofPromise (task : IO (IO.Promise (Except IO.Error α))) (error : String := "the promise linked to the Async was dropped") : Async α := do
  match ← task.toBaseIO with
  | .ok data => pure (f := BaseIO) <| MaybeTask.ofTask <| data.result?.map fun
    | none => .error error
    | some res => res
  | .error err => pure (f := BaseIO) (MaybeTask.pure (.error err))

/--
Converts `AsyncTask` into `Async`.
-/
@[inline]
protected def ofAsyncTask (task : AsyncTask α) : Async α := do
  pure (f := BaseIO) (MaybeTask.ofTask task)

/--
Converts `IO (Task α)` into `Async`.
-/
@[inline]
protected def ofIOTask (task : IO (Task α)) : Async α := do
  match ← task.toBaseIO with
  | .ok data => .ofAsyncTask (data.map Except.ok)
  | .error err => pure (f := BaseIO) (MaybeTask.pure (.error err))

/--
Converts `Except` to `Async`.
-/
@[inline]
protected def ofExcept (except : Except IO.Error α) : Async α :=
  pure (f := BaseIO) (MaybeTask.pure except)

/--
Converts `Task` to `Async`.
-/
@[inline]
protected def ofTask (task : Task α) : Async α := do
  .ofAsyncTask (task.map Except.ok)

/--
Converts `IO (IO.Promise α)` to `Async`.
-/
@[inline]
protected def ofPurePromise (task : IO (IO.Promise α)) (error : String := "the promise linked to the Async was dropped") : Async α := show BaseIO _ from do
  match ← task.toBaseIO with
  | .ok data => pure <| MaybeTask.ofTask <| data.result?.map fun
    | none => .error error
    | some res => pure res
  | .error err => pure (MaybeTask.pure (.error err))

@[default_instance]
instance : MonadAsync AsyncTask Async :=
  inferInstanceAs (MonadAsync (ETask IO.Error) (EAsync IO.Error))

instance : MonadAwait AsyncTask Async :=
  inferInstanceAs (MonadAwait AsyncTask (EAsync IO.Error))

instance : MonadAwait IO.Promise Async :=
  inferInstanceAs (MonadAwait IO.Promise (EAsync IO.Error))

/--
Runs two computations concurrently and returns both results as a pair.
-/
@[inline, specialize]
def concurrently (x : Async α) (y : Async β) (prio := Task.Priority.default) : Async (α × β) := do
  let taskX ← MonadAsync.async x (prio := prio)
  let taskY ← MonadAsync.async y (prio := prio)
  let resultX ← MonadAwait.await taskX
  let resultY ← MonadAwait.await taskY
  return (resultX, resultY)

/--
Runs two computations concurrently and returns the result of the one that finishes first.
The other result is lost and the other task is not cancelled, so the task will continue the execution
until the end.
-/
@[inline, specialize]
def race [Inhabited α] (x : Async α) (y : Async α)
    (prio := Task.Priority.default) :
    Async α := do
  let promise ← IO.Promise.new

  let task₁ ← MonadAsync.async (t := AsyncTask) (prio := prio) x
  let task₂ ← MonadAsync.async (t := AsyncTask) (prio := prio) y

  BaseIO.chainTask task₁ (liftM ∘ promise.resolve)
  BaseIO.chainTask task₂ (liftM ∘ promise.resolve)

  let result ← MonadAwait.await promise
  Async.ofExcept result

/--
Runs all computations in an `Array` concurrently and returns all results as an array.
-/
@[inline, specialize]
def concurrentlyAll (xs : Array (Async α)) (prio := Task.Priority.default) : Async (Array α) := do
  let tasks : Array (AsyncTask α) ← xs.mapM (MonadAsync.async (prio := prio))
  tasks.mapM MonadAwait.await

/--
Runs all computations concurrently and returns the result of the first one to finish.
All other results are lost, and the tasks are not cancelled, so they'll continue their execution
until the end.
-/
@[inline, specialize]
def raceAll [ForM Async c (Async α)] (xs : c) (prio := Task.Priority.default) : Async α := do
  let promise ← IO.Promise.new

  ForM.forM xs fun x => do
    let task₁ ← MonadAsync.async (t := AsyncTask) (prio := prio) x
    BaseIO.chainTask task₁ (liftM ∘ promise.resolve)

  let result ← MonadAwait.await promise
  Async.ofExcept result

end Async

export MonadAsync (async)
export MonadAwait (await)

/--
This function transforms the operation inside the monad `m` into a task and let it run in the background.
-/
@[inline, specialize]
def background [Monad m] [MonadAsync t m] (action : m α) (prio := Task.Priority.default) : m Unit :=
  discard (async (t := t) (prio := prio) action)

end Async
end IO
end Internal
end Std
