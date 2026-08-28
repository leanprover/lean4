/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Init.Data.Random
public import Std.Async.Basic
import Init.Data.ByteArray.Extra
import Init.Data.Array.Lemmas
import Init.Omega

public section

/-!
This module contains the implementation of a fair and data-loss free IO multiplexing primitive.
The main entrypoint for users is `Selectable.one` and the various functions to produce
`Selector`s from other modules.
-/

namespace Std
namespace Async

/--
The core data structure for racing on winning a `Selectable.one` if multiple event sources are ready
at the same time. A `Task` can try to finish the waiter by calling `Waiter.race`.
-/
structure Waiter (α : Type) where
  private mk ::
    private finished : IO.Ref Bool
    promise : IO.Promise (Except IO.Error α)

/--
Swap out the `IO.Promise` within the `Waiter`. Note that the part which determines whether the
`Waiter` is finished is not swapped out.
-/
@[inline]
def Waiter.withPromise (w : Waiter α) (p : IO.Promise (Except IO.Error β)) : Waiter β :=
  Waiter.mk w.finished p

/--
Try to atomically finish the `Waiter`. If the race for finishing it is won, `win` is executed
with the internal `IO.Promise` of the `Waiter`. This promise must under all circumstances be
resolved by `win`. If the race is lost some cleanup work can be done in `lose`.
-/
@[specialize]
def Waiter.race [Monad m] [MonadLiftT (ST IO.RealWorld) m] (w : Waiter α)
    (lose : m β) (win : IO.Promise (Except IO.Error α) → m β) : m β := do
  let first ← w.finished.modifyGet fun s => (s == false, true)
  if first then
    win w.promise
  else
    lose

/--
Atomically checks whether the `Waiter` has already finished. Note that right after this function
call ends this might have already changed.
-/
@[inline]
def Waiter.checkFinished [Monad m] [MonadLiftT (ST IO.RealWorld) m] (w : Waiter α) : m Bool := do
  w.finished.get

/--
An event source that can be multiplexed using `Selectable.one`, see the documentation of
`Selectable.one` for how the protocol of communicating with a `Selector` works.
-/
structure Selector (α : Type) where
  /--
  Attempts to retrieve a piece of data from the event source in a non-blocking fashion, returning
  `some` if data is available and `none` otherwise.
  -/
  tryFn : Async (Option α)
  /--
  Registers a `Waiter` with the event source. Once data is available, the event source should
  attempt to call `Waiter.race` and resolve the `Waiter`'s promise if it wins. It is crucial that
  data is never actually consumed from the event source unless `Waiter.race` wins in order to
  prevent data loss.
  -/
  registerFn : Waiter α → Async Unit
  /--
  A cleanup function that is called once any `Selector` has won the `Selectable.one` race.
  -/
  unregisterFn : Async Unit

/--
An event source together with a continuation to call on data obtained from that event source,
usually used together in conjunction with `Selectable.one`.
-/
structure Selectable (α : Type) where
  case ::
    {β : Type}
    /--
    The event source.
    -/
    selector : Selector β
    /--
    The continuation that is called on results from the event source.
    -/
    cont : β → Async α

private def shuffleIt {α : Type u} (xs : Array α) (gen : StdGen) : Array α × StdGen :=
  go xs gen 0
where
  go (xs : Array α) (gen : StdGen) (i : Nat) : Array α × StdGen :=
    if _ : i < xs.size - 1 then
      let (j, gen) := randNat gen i (xs.size - 1)
      let xs := xs.swapIfInBounds i j
      go xs gen (i + 1)
    else
      (xs, gen)

/--
Creates a `Selector` that performs fair and data-loss free multiplexing on multiple `Selectable`s.
This allows the multiplexing operation to be composed with other selectors.

The returned `Selector` polls and registers the `selectables` in random order for fairness. If
registering with one of them fails, the error is reported through the `Waiter` unless the race
was already won, in which case the winner's result takes priority.
-/
def Selectable.combine (selectables : Array (Selectable α)) : IO (Selector α) := do
  return {
    tryFn := do
      let gen ← IO.stdGenRef.get
      let (selectables, gen) := shuffleIt selectables gen
      IO.stdGenRef.set gen

      for selectable in selectables do
        if let some val ← selectable.selector.tryFn then
          return some (← selectable.cont val)

      return none

    registerFn := fun waiter => do
      let gen ← IO.stdGenRef.get
      let (selectables, gen) := shuffleIt selectables gen
      IO.stdGenRef.set gen

      for selectable in selectables do
        if ← waiter.checkFinished then
          return

        let waiterPromise ← IO.Promise.new

        try
          selectable.selector.registerFn (waiter.withPromise waiterPromise)
        catch e =>
          waiter.race (lose := pure ()) (win := fun promise => promise.resolve (.error e))
          return

        discard <| IO.bindTask (t := waiterPromise.result?) fun res? => do
          match res? with
          | none =>
            return (Task.pure (.ok ()))
          | some res =>
            let deliver : Async Unit :=
              try
                let val ← IO.ofExcept res
                waiter.promise.resolve (.ok (← selectable.cont val))
              catch e =>
                waiter.promise.resolve (.error e)

            deliver.toBaseIO

    unregisterFn := do
      for selectable in selectables do
        try selectable.selector.unregisterFn catch _ => pure ()
  }

/--
Performs fair and data-loss free multiplexing on the `Selectable`s in `selectables`.

`selectables` is combined into a single `Selector` via `Selectable.combine`:
1. If `Selector.tryFn` immediately yields a value, the corresponding `Selectable.cont` is
   executed and its result is returned immediately.
2. Otherwise, a single `Waiter` is registered with the combined `Selector` using
   `Selector.registerFn`. Once the `Waiter` is resolved, `Selector.unregisterFn` is called
   unconditionally, cleaning up every entry of `selectables`, before the result (or error) is
   returned to the caller. This holds no matter how the race is decided: a winning result, an
   error raised while resolving the `Waiter`, or a `registerFn` that throws mid-registration.
-/
def Selectable.one (selectables : Array (Selectable α)) : Async α := do
  if selectables.isEmpty then
    throw <| .userError "Selectable.one requires at least one Selectable"

  let selector ← Selectable.combine selectables

  if let some val ← selector.tryFn then
    return val

  let promise ← IO.Promise.new

  try
    selector.registerFn (Waiter.mk (← IO.mkRef false) promise)
    Async.ofPromise (pure promise)
  finally
    selector.unregisterFn

/--
Performs fair and data-loss free non-blocking multiplexing on the `Selectable`s in `selectables`.

This function only tries the non-blocking `tryFn` for each `Selectable` without registering
waiters or blocking. It returns `some result` if any `Selectable` is immediately available,
or `none` if all would block.

The protocol for this is as follows:
1. The `selectables` are shuffled randomly for fairness.
2. Run `Selector.tryFn` for each element in `selectables`. If any succeed, the corresponding
   `Selectable.cont` is executed and its result is returned as `some result`.
3. If none succeed, `none` is returned immediately without blocking.
-/
def Selectable.tryOne (selectables : Array (Selectable α)) : Async (Option α) := do
  if selectables.isEmpty then
    throw <| .userError "Selectable.tryOne requires at least one Selectable"

  let gen ← IO.stdGenRef.get
  let (selectables, gen) := shuffleIt selectables gen
  IO.stdGenRef.set gen

  for selectable in selectables do
    if let some val ← selectable.selector.tryFn then
      return some (← selectable.cont val)

  return none

end Async
end Std
