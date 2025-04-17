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

/--
A `Task` that may resolve to a value or an `IO.Error`.
-/
def AsyncTask (α : Type u) : Type u := Task (Except IO.Error α)

namespace AsyncTask

/--
Construct an `AsyncTask` that is already resolved with value `x`.
-/
@[inline]
protected def pure (x : α) : AsyncTask α := Task.pure <| .ok x

instance : Pure AsyncTask where
  pure := AsyncTask.pure

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
def bindIO (x : AsyncTask α) (f : α → IO (AsyncTask β)) : BaseIO (AsyncTask β) :=
  IO.bindTask x fun r =>
    match r with
    | .ok a => f a
    | .error e => .error e

/--
Similar to `bind`, however `f` has access to the `IO` monad. If `f` throws an error, the returned
`AsyncTask` resolves to that error.
-/
@[inline]
def mapIO (f : α → IO β) (x : AsyncTask α) : BaseIO (AsyncTask β) :=
  IO.mapTask (t := x) fun r =>
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
A `MaybeTask α` represents a computation that either:
- has already completed with a result (`pure`), or
- is an `AsyncTask α` that will eventually produce a result.
-/
inductive MaybeTask (α : Type)
  | pure : α → MaybeTask α
  | ofTask : AsyncTask α → MaybeTask α

instance : Pure MaybeTask :=
  ⟨MaybeTask.pure⟩

instance : MonadLift AsyncTask MaybeTask :=
  ⟨MaybeTask.ofTask⟩

instance : Coe α (MaybeTask α) :=
  ⟨MaybeTask.pure⟩

namespace MaybeTask

/--
Constructs an `AsyncTask` from a `MaybeTask`.
-/
@[inline]
def toTask : MaybeTask α → AsyncTask α
  | .pure a => .pure a
  | .ofTask t => t

/--
Gets the value of the `MaybeTask` by blocking on the possible inside of it `AsyncTask`.
-/
@[inline]
def wait {α : Type} (x : MaybeTask α) : IO α :=
  match x with
  | .pure a => Pure.pure a
  | .ofTask t => t.block

/--
Join the `MaybeTask` to an `AsyncTask`.
-/
@[inline]
def joinTask (t : AsyncTask (MaybeTask α)) : AsyncTask α :=
  t.bind fun
    | .pure a => .pure a
    | .ofTask t => t

/--
Creates an empty `MaybeTask` that resolves to `Unit`.
-/
@[inline]
def map (f : α → β) (t : MaybeTask α) : MaybeTask β :=
  match t with
  | .pure a => f a
  | .ofTask t => t.map f

/--
Chains two `MaybeTasks` together.
-/
@[inline]
protected def bind (t : MaybeTask α) (f : α → MaybeTask β) : MaybeTask β :=
  match t with
  | .pure a => f a
  | .ofTask t => t.bind (f · |>.toTask)

end MaybeTask

def Async (α : Type) := IO (Async.MaybeTask α)

namespace Async

/--
Creates an `Async` computation from an `IO (MaybeTask α)`.
-/
@[inline]
def mk (x : IO (MaybeTask α)) : Async α :=
  x

/--
Converts a normal `IO` computation into an `AsyncTask` that can be awaited.
-/
@[inline]
def asAsyncTask (x : IO α) : BaseIO (AsyncTask α) :=
  IO.asTask x

/--
Lifts an `Async` computation into an `AsyncTask` that can be awaited and joined.
-/
@[inline]
protected def asTask (x : Async α) : BaseIO (AsyncTask α) := do
  MaybeTask.joinTask <$> asAsyncTask x

/--
Binds a `MaybeTask` using a function that returns an `Async`.
-/
@[inline]
def bindIO (t : MaybeTask α) (f : α → Async β) : Async β := Async.mk <|
  match t with
  | .pure a => f a
  | .ofTask t => .ofTask <$> t.bindIO (MaybeTask.toTask <$> f ·)

/--
Creates an `Async` computation that immediately returns the given value.
-/
@[inline]
protected def pure (a : α) : Async α :=
  mk <| pure <| .pure a

/--
Lifts a regular `IO` action into an `Async` computation.
-/
@[inline]
protected def lift (x : IO α) : Async α :=
  mk <| .pure <$> x

/--
Returns the `Async` computation insside a the `AsyncTask`, so it can be awaited.
-/
@[inline]
def async (self : Async α) : Async (AsyncTask α) :=
  Async.lift <| self.asTask

/--
Converts the `Async` computation into its underlying `IO (MaybeTask α)` form.
This allows you to run the `Async` in a plain IO context.
-/
@[inline]
def toIO (self : Async α) : IO (MaybeTask α) :=
  self

/--
Waits for the result of the `Async` computation, blocking if necessary.
-/
@[inline]
protected def wait (self : Async α) : IO α :=
  self.toIO >>= MaybeTask.wait

/--
Maps the result of an `Async` computation with a pure function.
-/
@[inline]
protected def map (f : α → β) (self : Async α) : Async β :=
  mk <| (·.map f) <$> self.toIO

/--
Chains two `Async` computations together.
-/
@[inline]
protected def bind (self : Async α) (f : α → Async β) : Async β :=
  mk <| self.toIO >>= (bindIO · f)

/--
Raises an `IO.Error` within the `Async` monad.
-/
@[inline]
protected def throw (e : IO.Error) : Async α :=
  .error e

/--
Handles errors in an `Async` computation by running a handler if one occurs.
Equivalent to `try ... catch ...` in imperative languages.
-/
@[inline]
protected def tryCatch (x : Async α) (f : IO.Error → Async α) : Async α := fun w =>
    match x w with
    | .ok (.pure a) s => .ok a s
    | .ok (.ofTask t) s => .ok (.ofTask (Task.bind t (catcher f))) s
    | .error a s => .error a s
  where
    catcher {α} (f : IO.Error → Async α) :  Except IO.Error α → Task (Except IO.Error α)
      | .ok res => Task.pure (.ok res)
      | .error res =>
        match f res () with
        | .ok (.pure a) _ => Task.pure (.ok a)
        | .ok (.ofTask t) _ => t
        | .error a _ => Task.pure (.error a)

/--
Class for types of Tasks that can be awaited by a `m`
-/
class Await (n : Type → Type) (m : Type → Type) where
  await : n α → m α

instance : Await (IO ∘ AsyncTask) Async where
  await t := mk <| .ofTask <$> t

instance : Await AsyncTask Async where
  await t := mk <| pure <| .ofTask t

instance : Await IO.Promise Async where
  await t := mk <| pure <| .ofTask (t.result!.map (.ok))

instance : Functor Async where
  map := Async.map

instance : Monad Async where
  pure := Async.pure
  bind := Async.bind

instance : MonadLift IO Async :=
  ⟨Async.lift⟩

instance : MonadExcept IO.Error Async where
  throw := Async.throw
  tryCatch := Async.tryCatch

instance : MonadExceptOf IO.Error Async where
  throw := Async.throw
  tryCatch := Async.tryCatch

instance : OrElse (Async α) where
  orElse := MonadExcept.orElse

instance : Inhabited (Async α) where
  default := .error default

instance : MonadFinally Async where
  tryFinally' x f := fun w =>
    match x w with
    | .ok (.pure a) s => match f (some a) s with
      | .ok (.pure b) s => .ok (.pure (a, b)) s
      | .ok (.ofTask b) s => .ok (b.map (a, ·)) s
      | .error e s => .error e s
    | .ok (.ofTask a) s => .ok (a.bind fun a => match f (some a) s with
      | .ok (.pure b) _ => AsyncTask.pure (a, b)
      | .ok (.ofTask b) _ => b.map (a, ·)
      | .error e _ => Task.pure (.error e)
      ) s
    | .error a s => match f none s with
      | .ok (.pure _) s => .error a s
      | .ok (.ofTask b) s => .ok (.ofTask <| Task.map (fun
        | .ok _ => .error a
        | .error b => .error b) b) s
      | .error e s => .error e s

/--
Starts the given `AsyncTask` in the background and discards the result.
-/
@[inline]
def parallel {α : Type} (x : Async (AsyncTask α)) : Async Unit :=
  discard <| x

export Await (await)

end Async

export Async (await async parallel)

end Async
end IO
end Internal
end Std
