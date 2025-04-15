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

structure Selector (α : Type) where
  registerFn : IO.Promise Unit → IO Unit
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

    let promise ← IO.Promise.new

    for selectable in selectables do
      selectable.selector.registerFn promise

    -- We know for sure that `promise` will be resolved eventually
    IO.bindTask promise.result! (fun _ => go selectables)

def Sleep.selector (s : Sleep) : IO (Selector Unit) := do
  let waiter ← s.wait
  return {
    registerFn := fun promise => do
      discard <| AsyncTask.mapIO (x := waiter) fun _ => promise.resolve ()
    tryFn := do
      if (← IO.getTaskState waiter) == .finished then
        return some ()
      else
        return none
    unregisterFn := pure ()
  }

def TCP.Socket.Client.recvSelector (s : TCP.Socket.Client) (size : UInt64) :
    IO (Selector (Option ByteArray)) := do
  let waiter ← s.native.waitReadable
  return {
    registerFn := fun promise => do
      discard <| IO.mapTask (t := waiter.result?) fun res => do
        match res with
        | none => return ()
        | some res =>
          -- TODO: error handling interesting here
          discard <| IO.ofExcept res
          promise.resolve ()
    tryFn := do
      if (← IO.getTaskState waiter.result?) == .finished then
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


def test3 : IO (AsyncTask String) := do
  let client ← TCP.Socket.Client.mk
  let addr := Net.SocketAddressV4.mk (.ofParts 127 0 0 1) 8080
  IO.println "connecting"
  let task ← client.connect addr
  task.block
  IO.println "connected"

  let timeout ← Sleep.mk 5000
  Selectable.one #[
    .case (← timeout.selector) fun _ => return AsyncTask.pure "No no",
    .case (← client.readSelector 4096) fun data? => do
      if let some data := data? then
        return AsyncTask.pure <| String.fromUTF8! data
      else
        return AsyncTask.pure "Connection closed"
  ]

#eval show IO _ from do
  IO.println (← IO.ofExcept (← test3).get)

end Async
end IO
end Internal
end Std
