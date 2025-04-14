/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Init.Data.Array.Basic
import Init.Data.Random
import Std.Internal.Async.Timer

namespace Std
namespace Internal
namespace IO
namespace Async

structure Selector (α : Type) where
  registerFn : IO.Promise Unit → IO Unit
  tryFn : IO (Option α)

structure Selectable (α : Type) where
  case ::
    {β : Type}
    selector : Selector β
    cont : β → IO (AsyncTask α)


private def shuffleIt {α : Type u} (xs : Array α) (gen : StdGen) : Array α := Id.run do
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
  go selectables
where
  go (selectables : Array (Selectable α)) : IO (AsyncTask α) := do
    for selectable in selectables do
      if let some val ← selectable.selector.tryFn then
        return  (← selectable.cont val)

    let promise ← IO.Promise.new

    for selectable in selectables do
      selectable.selector.registerFn promise

    AsyncTask.bindIO (promise.result!.map (sync := true) .ok) (fun _ => go selectables)

def Sleep.selector (s : Sleep) : IO (Selector Unit) := do
  let waiter ← s.wait
  return {
    registerFn := fun promise => do
      discard <| AsyncTask.mapIO (x := waiter) fun _ => promise.resolve ()
    tryFn := do
      -- TODO: better wait mechanism?
      let state ← IO.getTaskState waiter
      if state == .finished then
        return some ()
      else
        return none
  }


def test1 : IO (AsyncTask Nat) := do
  let s1 ← Sleep.mk 100
  let s2 ← Sleep.mk 200
  Selectable.one #[
    .case (← s2.selector) fun _ => return AsyncTask.pure 2,
    .case (← s1.selector) fun _ => return AsyncTask.pure 1,
  ]

#eval show IO _ from do
  let task ← test1
  IO.ofExcept task.get

def test2 : IO (AsyncTask Nat) := do
  let s1 ← Sleep.mk 100
  Selectable.one #[
    .case (← s1.selector) fun _ => return AsyncTask.pure 1,
    .case (← s1.selector) fun _ => return AsyncTask.pure 2,
    .case (← s1.selector) fun _ => return AsyncTask.pure 3,
    .case (← s1.selector) fun _ => return AsyncTask.pure 4,
  ]

#eval show IO _ from do
  let task ← test2
  IO.ofExcept task.get

end Async
end IO
end Internal
end Std
