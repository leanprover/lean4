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

This module provides a layered approach to asynchronous programming, combining monadic interfaces,
type classes, and concrete task types that work together in a cohesive system.

- **Monadic Interfaces**: These types provide a good way to to chain and manipulate context. These
  can contain a `Task`, enabling manipulation of both asynchronous and synchronous code.
- **Concrete Task Types**: Concrete units of work that can be executed within these contexts.

## Monadic Interfaces

These types provide a good way to to chain and manipulate context. These can contain a `Task`,
enabling manipulation of both asynchronous and synchronous code.

- `BaseAsync`: A monadic interface for infallible asynchronous computations (alias for
  `EAsync Empty`)
- `EAsync`: A monadic interface for asynchronous computations that may fail with an error of type
  `ε`
- `Async`: A monadic interface for IO-based asynchronous computations that may fail with `IO.Error`
  (alias for `EAsync IO.Error`)

## Concurrent Units of Work

These are the concrete computational units that exist within the monadic contexts. These types
should not be created directly.

- `ETask`: A task that may fail with an error of type `ε`
- `AsyncTask`: A task that may fail with an `IO.Error` (alias for `ETask IO.Error`)
- `EMaybeTask`: A computation that is either immediately available or an asynchronous task

## Relation

Concrete units of work that can be executed within these contexts.

These types are related by two functions in the type classes `MonadAsync` and `MonadAwait`: `async`
and `await`. The `async` function extracts a concrete asynchronous task from a computation inside
the monadic context. In effect, it makes the computation run in the background and returns a
task handle that can be awaited later. On the other side, the `await` function takes a task and
re-inserts it into the monadic context, allowing the result to be composed using the monadic bind.
This relation between `async` and `await` enables precise control over when a computation starts and
when its result is actually used. You can spawn multiple asynchronous tasks using `async`, continue
with other operations, and later rejoin the computation flow by awaiting their results.

These functions should not be used directly. Instead, prefer higher-level combinators such as
`race`, `raceAll`, `concurrently`, `background` and `concurrentlyAll`. The best way to think about
how to write your async code, it to avoid using the concurrent units of work, and only use it when integrating
with non async code that uses them.

-/

/--
Typeclass for monads that can "await" a computation of type `t α` in a monad `m` until the result is
available.
-/
class MonadAwait (t : Type → Type) (m : Type → Type) extends Monad m where
  /--
  Awaits the result of `t α` and returns it inside the `m` monad.
  -/
  await : t α → m α

/--
Represents monads that can launch computations asynchronously of type `t` in a monad `m`.
-/
class MonadAsync (t : Type → Type) (m : Type → Type) extends Monad m where
  /--
  Starts an asynchronous computation in another monad.
  -/
  async : m α → m (t α)

instance [Monad m] [MonadAwait t m] : MonadAwait t (StateT n m) where
  await := liftM (m := m) ∘ MonadAwait.await

instance [Monad m] [MonadAwait t m] : MonadAwait t (ExceptT n m) where
  await := liftM (m := m) ∘ MonadAwait.await

instance [Monad m] [MonadAwait t m] : MonadAwait t (ReaderT n m) where
  await := liftM (m := m) ∘ MonadAwait.await

instance [MonadAwait t m] : MonadAwait t (StateRefT' s n m) where
  await := liftM (m := m) ∘ MonadAwait.await

instance [MonadAwait t m] : MonadAwait t (StateT s m) where
  await := liftM (m := m) ∘ MonadAwait.await

instance [MonadAsync t m] : MonadAsync t (ReaderT n m) where
  async p := MonadAsync.async ∘ p

instance [MonadAsync t m] : MonadAsync t (StateRefT' s n m) where
  async p := MonadAsync.async ∘ p

instance [Functor t] [inst : MonadAsync t m] : MonadAsync t (StateT s m) where
  async p := fun s => do
    let t ← inst.async (p s)
    pure (t <&> Prod.fst, s)


/--
A `Task` that may resolve to either a value of type `α` or an error value of type `ε`.
-/
def ETask (ε : Type) (α : Type u) : Type u := Task (Except ε α)

namespace ETask

/--
Construct an `ETask` that is already resolved with value `x`.
-/
@[inline]
protected def pure (x : α) : ETask ε α :=
  Task.pure <| .ok x

/--
Create a new `ETask` that will run after `x` has finished.

If `x`:
- errors, return an `ETask` that resolves to the error.
- succeeds, return an `ETask` that resolves to `f x`.
-/
@[inline]
protected def map (f : α → β) (x : ETask ε α) : ETask ε β :=
  Task.map (x := x) fun r =>
    match r with
    | .ok a => .ok (f a)
    | .error e => .error e

/--
Creates a new `ETask` that will run after `x` has completed. If `x`:
- errors, return an `ETask` that resolves to the error.
- succeeds, run `f` on the result of `x` and return the `ETask` produced by `f`.
-/
@[inline]
protected def bind (x : ETask ε α) (f : α → ETask ε β) : ETask ε β :=
  Task.bind x fun r =>
    match r with
    | .ok a => f a
    | .error e => Task.pure <| .error e

/--
Similar to `bind`, however `f` has access to the `IO` monad. If `f` throws an error, the returned
`ETask` resolves to that error.
-/
@[inline]
protected def bindIO (x : ETask ε α) (f : α → EIO ε (ETask ε β)) : EIO ε (ETask ε β) :=
  EIO.bindTask x fun r =>
    match r with
    | .ok a => f a
    | .error e => .error e

/--
Similar to `bind`, however `f` has access to the `IO` monad. If `f` throws an error, the returned
`ETask` resolves to that error.
-/
@[inline]
protected def mapIO (f : α → EIO ε β) (x : ETask ε α) : BaseIO (ETask ε β) :=
  EIO.mapTask (t := x) fun r =>
    match r with
    | .ok a => f a
    | .error e => .error e

/--
Block until the `ETask` in `x` finishes and returns its value. Propagates any error encountered
during execution.
-/
@[inline]
protected def block (x : ETask ε α) : EIO ε α := do
  let res := x.get
  match res with
  | .ok a => return a
  | .error e => .error e

/--
Create an `ETask` that resolves to the value of the promise `x`.
-/
@[inline]
def ofPromise (x : IO.Promise (Except ε α)) : ETask ε α :=
  x.result!

/--
Create an `ETask` that resolves to the pure value of the promise `x`.
-/
@[inline]
def ofPurePromise (x : IO.Promise α) : ETask ε α :=
  x.result!.map pure

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
protected def mapIO (f : α → IO β) (x : AsyncTask α) : BaseIO (AsyncTask β) :=
  EIO.mapTask (t := x) fun r =>
    match r with
    | .ok a => f a
    | .error e => .error e

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
Similar to `map`, however `f` has access to the `IO` monad. If `f` throws an error, the returned
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
A `EMaybeTask ε α` represents a computation that either:

- Is immediately available as an `α` value, or
- Is an asynchronous computation that will eventually produce an `α` value or an error `ε`
-/
inductive EMaybeTask (ε : Type) (α : Type)
  | pure : α → EMaybeTask ε α
  | ofTask : ETask ε α → EMaybeTask ε α

namespace EMaybeTask

/--
Constructs an `ETask` from a `EMaybeTask`.
-/
@[inline]
def toTask : EMaybeTask ε α → ETask ε α
  | .pure a => .pure a
  | .ofTask t => t

/--
Gets the value of the `EMaybeTask` by blocking on the possible inside `ETask`.
-/
@[inline]
def wait {α : Type} (x : EMaybeTask ε α) : EIO ε α :=
  match x with
  | .pure a => Pure.pure a
  | .ofTask t => t.block

/--
Maps a function over a `EMaybeTask`.
-/
@[inline]
def map (f : α → β) (t : EMaybeTask ε α) : EMaybeTask ε β :=
  match t with
  | .pure a => .pure <| f a
  | .ofTask t => .ofTask <| t.map f

/--
Sequences two computations, allowing the second to depend on the value computed by the first.
-/
@[inline]
protected def bind (t : EMaybeTask ε α) (f : α → EMaybeTask ε β) : EMaybeTask ε β :=
  match t with
  | .pure a => f a
  | .ofTask t => .ofTask <| t.bind (f · |>.toTask)

/--
Join the `EMaybeTask` to an `ETask`.
-/
@[inline]
def joinTask (t : ETask ε (EMaybeTask ε α)) : ETask ε α :=
  t.bind fun
    | .pure a => .pure a
    | .ofTask t => t

instance : Functor (EMaybeTask ε) where
  map := EMaybeTask.map

instance : Monad (EMaybeTask ε) where
  pure := EMaybeTask.pure
  bind := EMaybeTask.bind

end EMaybeTask

/--
An asynchronous computation that may produce an error of type `ε`.
-/
structure EAsync (ε : Type) (α : Type) where
  toRawEIO : EIO ε (Async.EMaybeTask ε α)

namespace EAsync

/--
Converts a `EAsync` to a `ETask`.
-/
@[inline]
protected def toEIO (x : EAsync ε α) : EIO ε (ETask ε α) :=
  EMaybeTask.toTask <$> x.toRawEIO

/--
Creates a new `EAsync` out of a `Task`.
-/
@[inline]
protected def ofTask (x : Task α) : EAsync ε α :=
  .mk (pure (EMaybeTask.ofTask <| x.map (.ok)))

/--
Creates a new `EAsync` out of a `ETask`.
-/
@[inline]
protected def ofETask (x : ETask ε α) : EAsync ε α :=
  .mk (pure (EMaybeTask.ofTask x))

/--
Creates an `EAsync` computation that immediately returns the given value.
-/
@[inline]
protected def pure (a : α) : EAsync ε α :=
  .mk <| pure <| .pure a

/--
Maps the result of an `EAsync` computation with a pure function.
-/
@[inline]
protected def map (f : α → β) (self : EAsync ε α) : EAsync ε β :=
  mk <| (·.map f) <$> self.toRawEIO

/--
Maps the result of an `EAsync` computation with a pure function.
-/
@[inline]
protected def toTask (f : α → β) (self : EAsync ε α) : EAsync ε β :=
  mk <| (·.map f) <$> self.toRawEIO

/--
Sequences two computations, allowing the second to depend on the value computed by the first.
-/
@[inline]
protected def bind (self : EAsync ε α) (f : α → EAsync ε β) : EAsync ε β :=
  mk <| self.toRawEIO >>= (bindAsyncTask · f |>.toRawEIO)
where
  bindAsyncTask (t : EMaybeTask ε α) (f : α → EAsync ε β) : EAsync ε β := .mk <|
    match t with
    | .pure a => f a |>.toRawEIO
    | .ofTask t => .ofTask <$> t.bindIO (fun s => EMaybeTask.toTask <$> (f s |>.toRawEIO))

/--
Lifts an `EIO` action into an `EAsync` computation.
-/
@[inline]
protected def lift (x : EIO ε α) : EAsync ε α :=
  .mk <| (.pure ∘ .pure) =<< x

/--
Waits for the result of the `EAsync` computation, blocking if necessary.
-/
@[inline]
protected def wait (self : EAsync ε α) : EIO ε α :=
  self.toRawEIO >>= EMaybeTask.wait

/--
Lifts an `EAsync` computation into an `ETask` that can be awaited and joined.
-/
@[inline]
protected def asTask (x : EAsync ε α) : EIO ε (ETask ε α) := do
  EMaybeTask.joinTask <$> EIO.asTask x.toRawEIO

/--
Raises an error of type `ε` within the `EAsync` monad.
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
      | .ok (.pure b) _ => ETask.pure (a, b)
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
Creates an `EAsync` computation that awaits the completion of the given `ETask ε α`.
-/
@[inline]
def await (x : ETask ε α) : EAsync ε α :=
  EAsync.mk (pure <| EMaybeTask.ofTask x)

/--
Returns the `EAsync` computation inside an `ETask ε α`, so it can be awaited.
-/
@[inline]
def async (self : EAsync ε α) : EAsync ε (ETask ε α) :=
  EAsync.lift <| self.asTask

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

instance : MonadAwait (ETask ε) (EAsync ε) where
  await t := mk <| pure <| .ofTask t

instance : MonadAwait Task (EAsync ε) where
  await t := mk <| pure <| .ofTask (t.map (.ok))

instance : MonadAwait AsyncTask (EAsync IO.Error) where
  await t := mk <| pure <| .ofTask t

instance : MonadAwait IO.Promise (EAsync ε) where
  await t := mk <| pure <| .ofTask (t.result!.map (.ok))

instance : MonadAsync (ETask ε) (EAsync ε) where
  async t := EAsync.lift <| t.asTask

instance : MonadAsync AsyncTask (EAsync IO.Error) where
  async t := EAsync.lift <| t.asTask

/--
A tail recursive version of the `forIn` for while loops inside the `EAsync` Monad.
-/
@[inline]
protected partial def forIn {β : Type} [i : Inhabited ε] (init : β) (f : Unit → β → EAsync ε (ForInStep β)) : EAsync ε β := do
  let promise ← IO.Promise.new

  let rec @[specialize] loop (b : β) : EAsync ε (ETask ε Unit) := async do
    match ← f () b with
      | ForInStep.done b => promise.resolve (.ok b)
      | ForInStep.yield b => discard <| (loop b)

  discard <| loop init

  .mk <| pure <| .ofTask promise.result!

instance eta [Inhabited ε] : ForIn (EAsync ε) Lean.Loop Unit where
  forIn _ := EAsync.forIn

end EAsync

/--
An asynchronous computation that may produce an error of type `IO.Error`.
Alias for `EAsync IO.Error`.
-/
abbrev Async (α : Type) := EAsync IO.Error α

namespace Async

/--
Converts a `Async` to a `AsyncTask`.
-/
@[inline]
protected def toIO (x : Async α) : IO (AsyncTask α) :=
  EMaybeTask.toTask <$> x.toRawEIO

/--
Waits for the result of the `Async` computation, blocking if necessary.
-/
@[inline]
protected def wait (self : Async α) : IO α :=
  self.toRawEIO >>= EMaybeTask.wait

/--
Lifts an `Async` computation into an `AsyncTask` that can be awaited and joined.
-/
@[inline]
def asTask (x : Async α) : IO (AsyncTask α) := do
  EMaybeTask.joinTask <$> IO.asTask x.toRawEIO

/--
Returns the `Async` computation inside an `AsyncTask`, so it can be awaited.
-/
@[inline]
def async (self : Async α) : Async (AsyncTask α) :=
  EAsync.lift <| self.asTask

instance : MonadAwait AsyncTask Async :=
  inferInstanceAs (MonadAwait AsyncTask (EAsync IO.Error))

@[default_instance]
instance : MonadAsync AsyncTask Async :=
  inferInstanceAs (MonadAsync (ETask IO.Error) (EAsync IO.Error))

instance : MonadAwait IO.Promise Async :=
  inferInstanceAs (MonadAwait IO.Promise (EAsync IO.Error))

end Async

/--
An asynchronous computation that cannot fail with any error.
Alias for `EAsync Empty`.
-/
abbrev BaseAsync (α : Type) := EAsync Empty α

namespace BaseAsync

/--
Converts a `Async` to a `AsyncTask`.
-/
@[inline]
protected def toBaseAsync (x : BaseAsync α) : BaseIO (Task α) := do
  let result ← EMaybeTask.toTask <$> x.toRawEIO
  return Task.map (fun (.ok r) => r) result

/--
Waits for the result of the `BaseAsync` computation, blocking if necessary.
-/
@[inline]
protected def wait (self : BaseAsync α) : BaseIO α :=
  self.toRawEIO >>= EMaybeTask.wait

/--
Lifts a `BaseAsync` computation into a `Task` that can be awaited and joined.
-/
@[inline]
def asTask (x : BaseAsync α) : EIO ε (Task α) := do
  let task ← EMaybeTask.joinTask <$> EIO.asTask x.toRawEIO
  return Task.map (prio := 0) (fun (.ok r) => r) task

/--
Creates a `BaseAsync` that awaits the completion of the given `Task α`.
-/
@[inline]
def await (t : Task α) : BaseAsync α :=
  .mk <| pure <| .ofTask <| t.map (fun x => .ok x)

/--
Returns the `BaseAsync` computation inside a `Task α`, so it can be awaited.
-/
@[inline]
def async (self : BaseAsync α) : BaseAsync (Task α) :=
  EAsync.lift <| self.asTask

instance : MonadAwait (ETask Empty) BaseAsync :=
  inferInstanceAs (MonadAwait (ETask Empty) (EAsync Empty))

instance : MonadAwait Task BaseAsync where
  await := BaseAsync.await

instance : MonadAsync Task BaseAsync where
  async := BaseAsync.async

instance : MonadAsync (ETask ε) BaseAsync where
  async := Functor.map (Task.map .ok) ∘ BaseAsync.async

instance : MonadLiftT BaseAsync (EAsync ε) where
  monadLift {α} x :=
    let r : EIO ε (EMaybeTask ε α) := do
      let r ← BaseIO.toEIO (x.toRawEIO)
      match r with
      | .pure res => pure <| .pure res
      | .ofTask t => pure <| .ofTask <| Task.map (fun (.ok t) => .ok t) t
    ⟨r⟩

instance : MonadLiftT BaseAsync Async :=
  inferInstanceAs (MonadLiftT BaseAsync (EAsync IO.Error))

end BaseAsync

export MonadAsync (async)
export MonadAwait (await)

/--
This function transforms the operation inside the monad `m` into a task and let it run in the background.
-/
@[inline, specialize]
def background [Monad m] [MonadAsync t m] : m α → m Unit :=
  discard ∘ async (t := t)

/--
Runs two computations concurrently and returns both results as a pair.
-/
@[inline, specialize]
def concurrently [Monad m] [MonadAwait t m] [MonadAsync t m] (x : m α) (y : m β) : m (α × β) := do
  let taskX : t α ← async x
  let taskY : t β ← async y
  let resultX ← await taskX
  let resultY ← await taskY
  return (resultX, resultY)

/--
Runs two computations concurrently and returns the result of the one that finishes first.
The other result is lost and the other task is not cancelled, so the task will continue the execution
until the end.
-/
@[inline, specialize]
def race [MonadLiftT BaseIO m] [MonadAwait Task m] [MonadAsync t m] [MonadAwait t m] [Monad m] [Inhabited α] (x : m α) (y : m α) : m α := do
  let promise ← IO.Promise.new

  discard (async (t := t) <| Bind.bind x (liftM ∘ promise.resolve))
  discard (async (t := t) <| Bind.bind y (liftM ∘ promise.resolve))

  await promise.result!

/--
Runs all computations in an `Array` concurrently and returns all results as an array.
-/
@[inline, specialize]
def concurrentlyAll [Monad m] [MonadAwait t m] [MonadAsync t m] (xs : Array (m α)) : m (Array α) := do
  let tasks : Array (t α) ← xs.mapM async
  tasks.mapM await

/--
Runs all computations concurrently and returns the result of the first one to finish.
All other results are lost, and the tasks are not cancelled, so they'll continue their executing
until the end.
-/
@[inline, specialize]
def raceAll [ForM m c (m α)] [MonadLiftT BaseIO m] [MonadAwait Task m] [MonadAsync t m] [MonadAwait t m] [Monad m] [Inhabited α] (xs : c) : m α := do
  let promise ← IO.Promise.new

  ForM.forM xs fun x =>
    discard (async (t := t) <| Bind.bind x (liftM ∘ promise.resolve))

  await promise.result!

end Async
end IO
end Internal
end Std
