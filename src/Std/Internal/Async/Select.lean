/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Init.Data.Array.Basic
import Init.Data.Random
import Std.Internal.Async.Basic

namespace Std
namespace Internal
namespace IO
namespace Async

structure Waiter (α : Type) where
  private mk ::
    finished : IO.Ref Bool
    signal : IO.Promise (Except IO.Error α)

def Waiter.new : BaseIO (Waiter α) := do
  return { finished := ← IO.mkRef false, signal := ← IO.Promise.new }

-- TODO: think about resolving the promise with errors thrown? Should make stuff easier
@[specialize]
def Waiter.race [Monad m] [MonadLiftT BaseIO m] (w : Waiter α)
    (loose : m β) (win : IO.Promise (Except IO.Error α) → m β) : m β := do
  let first ← liftM (m := BaseIO) <| w.finished.modifyGet fun s => (s == false, true)
  if first then
    win w.signal
  else
    loose

-- TODO: Once and if we have universe polymorphic IO this can go into registerFn
structure Selector (α : Type) (β : Type) where
  tryFn : IO (Option α)
  registerFn : (α → IO (AsyncTask β)) → Waiter β → IO Unit
  unregisterFn : IO Unit

structure Selectable (α : Type) where
  case ::
    {β : Type}
    selector : Selector β α
    cont : β → IO (AsyncTask α)

private def shuffleIt {α : Type u} (xs : Array α) (gen : StdGen) : Array α :=
  go xs gen 0
where
  go (xs : Array α) (gen : StdGen) (i : Nat) : Array α :=
    if _ : i < xs.size - 2 then
      let (j, gen) := randNat gen i (xs.size - 1)
      let xs := xs.swapIfInBounds i j
      go xs gen (i + 1)
    else
      xs

partial def Selectable.one (selectables : Array (Selectable α)) : IO (AsyncTask α) := do
  let seed := UInt64.toNat (ByteArray.toUInt64LE! (← IO.getRandomBytes 8))
  let gen := mkStdGen seed
  let selectables := shuffleIt selectables gen
  for selectable in selectables do
    if let some val ← selectable.selector.tryFn then
      return ← selectable.cont val

  let waiter ← Waiter.new

  for selectable in selectables do
    selectable.selector.registerFn selectable.cont waiter

  -- We know the promise will be resolved
  IO.mapTask (t := waiter.signal.result!) fun res => do
    for selectable in selectables do
      -- TODO: Think about error handling
      selectable.selector.unregisterFn

    IO.ofExcept res

end Async
end IO
end Internal
end Std
