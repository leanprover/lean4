/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude

import Init.Data.Array.Basic
import Init.Data.Random

import Std.Internal.Async.Timer
import Std.Internal.Async.TCP

namespace Std
namespace Internal
namespace IO
namespace Async

structure Waiter where
  private mk ::
    private finished : IO.Ref Bool
    private signal : IO.Promise Unit

def Waiter.new : BaseIO Waiter := do
  return { finished := ← IO.mkRef false, signal := ← IO.Promise.new }

def Waiter.resolve (w : Waiter) : BaseIO Bool := do
  let first ← w.finished.modifyGet fun s => (s == false, true)
  if first then
    w.signal.resolve ()
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
  go selectables
where
  go (selectables : Array (Selectable α)) : IO (AsyncTask α) := do
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

    let waiter ← Waiter.new

    for selectable in selectables do
      selectable.selector.registerFn waiter

    -- We know for sure that `signal` will be resolved eventually
    IO.bindTask waiter.signal.result! (fun _ => go selectables)

def Sleep.selector (s : Sleep) : IO (Selector Unit) := do
  let sleepWaiter ← s.wait
  return {
    registerFn := fun waiter => do
      discard <| AsyncTask.mapIO (x := sleepWaiter) fun _ => waiter.resolve
    tryFn := do
      if (← IO.getTaskState sleepWaiter) == .finished then
        return some ()
      else
        return none
    unregisterFn := pure ()
  }

def TCP.Socket.Client.recvSelector (s : TCP.Socket.Client) (size : UInt64) :
    IO (Selector (Option ByteArray)) := do
  let readWaiter ← s.native.waitReadable
  return {
    registerFn := fun waiter => do
      discard <| IO.mapTask (t := readWaiter.result?) fun res => do
        match res with
        | none => return ()
        | some res =>
          -- TODO: error handling interesting here
          discard <| IO.ofExcept res
          discard <| waiter.resolve
    tryFn := do
      if (← IO.getTaskState readWaiter.result?) == .finished then
        -- We know that this read should not block
        let res ← (← s.recv? size).block
        return some res
      else
        return none
    unregisterFn := s.native.cancelRecv
  }
  #exit
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
  let s2 ← Sleep.mk 100
  let s3 ← Sleep.mk 100
  let s4 ← Sleep.mk 100
  Selectable.one #[
    .case (← s1.selector) fun _ => return AsyncTask.pure 1,
    .case (← s2.selector) fun _ => return AsyncTask.pure 2,
    .case (← s3.selector) fun _ => return AsyncTask.pure 3,
    .case (← s4.selector) fun _ => return AsyncTask.pure 4,
  ]

#eval show IO _ from do
  IO.println (← IO.ofExcept (← test2).get)
  IO.println (← IO.ofExcept (← test2).get)
  IO.println (← IO.ofExcept (← test2).get)
  IO.println (← IO.ofExcept (← test2).get)
  IO.println (← IO.ofExcept (← test2).get)

end Async
end IO
end Internal
end Std
