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

structure Waiter where
  private mk ::
    private finished : IO.Ref Bool
    private signal : IO.Promise (Except IO.Error Unit)

def Waiter.new : BaseIO Waiter := do
  return { finished := ← IO.mkRef false, signal := ← IO.Promise.new }

def Waiter.resolve (w : Waiter) (res : Except IO.Error Unit) : BaseIO Bool := do
  let first ← w.finished.modifyGet fun s => (s == false, true)
  if first then
    w.signal.resolve res
  return first

structure Selector (α : Type) where
  registerFn : Waiter → IO Unit
  tryFn : IO (Option α)
  unregisterFn : IO Unit

structure Selectable (α : Type) where
  case ::
    {β : Type}
    selector : Selector β
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
  go selectables true
where
  go (selectables : Array (Selectable α)) (first : Bool) : IO (AsyncTask α) := do
    for h : i in [:selectables.size] do
      have := Membership.get_elem_helper h rfl
      let selectable := selectables[i]'this
      if let some val ← selectable.selector.tryFn then
        for h : j in [:selectables.size] do
          if j ≠ i then
            have := Membership.get_elem_helper h rfl
            let selectable := selectables[j]'this
            selectable.selector.unregisterFn

        return (← selectable.cont val)

    if !first then
      selectables.forM (·.selector.unregisterFn)

    let waiter ← Waiter.new

    for selectable in selectables do
      selectable.selector.registerFn waiter

    -- We know for sure that `signal` will be resolved eventually
    IO.bindTask waiter.signal.result! fun res => do
      match res with
      | .ok .. => go selectables false
      | .error e =>
        selectables.forM (·.selector.unregisterFn)
        throw e

end Async
end IO
end Internal
end Std
