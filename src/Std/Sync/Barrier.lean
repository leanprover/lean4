/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Sync.Mutex

namespace Std

/-
This file heavily inspired by:
https://github.com/rust-lang/rust/blob/b8ae372/library/std/src/sync/barrier.rs
-/

private structure BarrierState where
  count : Nat
  generationId : Nat

/--
A `Barrier` will block `n - 1` threads which call `Barrier.wait` and then wake up all threads at
once when the `n`-th thread calls `Barrier.wait`.
-/
structure Barrier where private mk ::
  private lock : Mutex BarrierState
  private cvar : Condvar
  numThreads : Nat

/--
Creates a new barrier that can block a given number of threads.
-/
def Barrier.new (numThreads : Nat) : BaseIO Barrier := do
  return {
    lock := ← Mutex.new { count := 0, generationId := 0 },
    cvar := ← Condvar.new,
    numThreads := numThreads
  }

/--
Blocks the current thread until all threads have rendezvoused here.

Barriers are re-usable after all threads have rendezvoused once, and can be used continuously.

A single (arbitrary) thread will receive `true` when returning from this function, and all other
threads will receive `false`.
-/
def Barrier.wait (barrier : Barrier) : BaseIO Bool := do
  barrier.lock.atomically do
    let localGen := (← get).generationId
    modify fun s => { s with count := s.count + 1 }
    if (← get).count < barrier.numThreads then
      barrier.cvar.waitUntil barrier.lock.mutex do
        return (← get).generationId != localGen
      return false
    else
      modify fun s => { count := 0, generationId := s.generationId + 1 }
      barrier.cvar.notifyAll
      return true

end Std
