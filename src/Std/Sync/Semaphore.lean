/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean FRO Contributors
-/
module

prelude
public import Std.Sync.Mutex

public section

namespace Std

/--
Counting semaphore.

`Semaphore.acquire` blocks until a permit is available. `Semaphore.release` adds one permit and
wakes one waiting thread.
-/
structure Semaphore where private mk ::
  private lock : Mutex Nat
  private cvar : Condvar

/--
Creates a new semaphore with `permits` initially available permits.
-/
def Semaphore.new (permits : Nat) : BaseIO Semaphore := do
  return { lock := ← Mutex.new permits, cvar := ← Condvar.new }

/--
Waits until a permit is available and then acquires it.
-/
def Semaphore.acquire (sem : Semaphore) : BaseIO Unit := do
  sem.lock.atomicallyOnce sem.cvar
    (return (← get) > 0)
    (modify fun permits => permits - 1)

/--
Tries to acquire a permit without blocking. Returns `true` on success.
-/
def Semaphore.tryAcquire (sem : Semaphore) : BaseIO Bool := do
  sem.lock.atomically do
    let permits ← get
    if permits > 0 then
      set (permits - 1)
      return true
    else
      return false

/--
Releases one permit and wakes one waiting thread, if any.
-/
def Semaphore.release (sem : Semaphore) : BaseIO Unit := do
  sem.lock.atomically do
    modify fun permits => permits + 1
  sem.cvar.notifyOne

/--
Returns the number of currently available permits.
-/
def Semaphore.availablePermits (sem : Semaphore) : BaseIO Nat :=
  sem.lock.atomically do
    get

end Std
