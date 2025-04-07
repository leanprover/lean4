/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
prelude
import Std.Sync.Basic

namespace Std

private opaque BaseMutexImpl : NonemptyType.{0}

/--
Mutual exclusion primitive (a lock).

If you want to guard shared state, use `Mutex α` instead.
-/
def BaseMutex : Type := BaseMutexImpl.type

instance : Nonempty BaseMutex := BaseMutexImpl.property

/-- Creates a new `BaseMutex`. -/
@[extern "lean_io_basemutex_new"]
opaque BaseMutex.new : BaseIO BaseMutex

/--
Locks a `BaseMutex`.  Waits until no other thread has locked the mutex.

The current thread must not have already locked the mutex.
Reentrant locking is undefined behavior (inherited from the C++ implementation).
If this is unavoidable in your code, consider using `BaseRecursiveMutex`.
-/
@[extern "lean_io_basemutex_lock"]
opaque BaseMutex.lock (mutex : @& BaseMutex) : BaseIO Unit

/--
Attempts to lock a `BaseMutex`. If the mutex is not available return `false`, otherwise lock it and
return `true`.

This function does not block.

The current thread must not have already locked the mutex.
Reentrant locking is undefined behavior (inherited from the C++ implementation).
If this is unavoidable in your code, consider using `BaseRecursiveMutex`.
-/
@[extern "lean_io_basemutex_try_lock"]
opaque BaseMutex.tryLock (mutex : @& BaseMutex) : BaseIO Bool

/--
Unlocks a `BaseMutex`.

The current thread must have already locked the mutex.
Unlocking an unlocked mutex is undefined behavior (inherited from the C++ implementation).
If this is unavoidable in your code, consider using `BaseRecursiveMutex`.
-/
@[extern "lean_io_basemutex_unlock"]
opaque BaseMutex.unlock (mutex : @& BaseMutex) : BaseIO Unit

private opaque CondvarImpl : NonemptyType.{0}

/--
Condition variable, a synchronization primitive to be used with a `BaseMutex` or `Mutex`.

The thread that wants to modify the shared variable must:
1. Lock the `BaseMutex` or `Mutex`
2. Work on the shared variable
3. Call `Condvar.notifyOne` or `Condvar.notifyAll` after it is done. Note that this may be done
   before or after the mutex is unlocked.

If working with a `Mutex` the thread that waits on the `Condvar` can use `Mutex.atomicallyOnce`
to wait until a condition is true. If working with a `BaseMutex` it must:
1. Lock the `BaseMutex`.
2. Do one of the following:
  - Use `Condvar.waitUntil` to (potentially repeatedly wait) on the condition variable until
     the condition is true.
  - Implement the waiting manually by:
    1. Checking the condition
    2. Calling `Condvar.wait` which releases the `BaseMutex` and suspends execution until the
       condition variable is notified.
    3. Check the condition and resume waiting if not satisfied.
-/
def Condvar : Type := CondvarImpl.type

instance : Nonempty Condvar := CondvarImpl.property

/-- Creates a new condition variable. -/
@[extern "lean_io_condvar_new"]
opaque Condvar.new : BaseIO Condvar

/-- Waits until another thread calls `notifyOne` or `notifyAll`. -/
@[extern "lean_io_condvar_wait"]
opaque Condvar.wait (condvar : @& Condvar) (mutex : @& BaseMutex) : BaseIO Unit

/-- Wakes up a single other thread executing `wait`. -/
@[extern "lean_io_condvar_notify_one"]
opaque Condvar.notifyOne (condvar : @& Condvar) : BaseIO Unit

/-- Wakes up all other threads executing `wait`. -/
@[extern "lean_io_condvar_notify_all"]
opaque Condvar.notifyAll (condvar : @& Condvar) : BaseIO Unit

/-- Waits on the condition variable until the predicate is true. -/
def Condvar.waitUntil [Monad m] [MonadLiftT BaseIO m]
    (condvar : Condvar) (mutex : BaseMutex) (pred : m Bool) : m Unit := do
  while !(← pred) do
    condvar.wait mutex

/--
Mutual exclusion primitive (lock) guarding shared state of type `α`.

The type `Mutex α` is similar to `IO.Ref α`, except that concurrent accesses are guarded by a mutex
instead of atomic pointer operations and busy-waiting.
-/
structure Mutex (α : Type) where private mk ::
  private ref : IO.Ref α
  mutex : BaseMutex
deriving Nonempty

instance : CoeOut (Mutex α) BaseMutex where coe := Mutex.mutex

/-- Creates a new mutex. -/
def Mutex.new (a : α) : BaseIO (Mutex α) :=
  return { ref := ← IO.mkRef a, mutex := ← BaseMutex.new }

/--
`mutex.atomically k` runs `k` with access to the mutex's state while locking the mutex.

Calling `mutex.atomically` while already holding the underlying `BaseMutex` in the same thread
is undefined behavior. If this is unavoidable in your code, consider using `RecursiveMutex`.
-/
def Mutex.atomically [Monad m] [MonadLiftT BaseIO m] [MonadFinally m]
    (mutex : Mutex α) (k : AtomicT α m β) : m β := do
  try
    mutex.mutex.lock
    k mutex.ref
  finally
    mutex.mutex.unlock

/--
`mutex.tryAtomically k` tries to lock `mutex` and runs `k` on it if it succeeds. On success the
return value of `k` is returned as `some`, on failure `none` is returned.

This function does not block on the `mutex`. Additionally calling `mutex.tryAtomically` while
already holding the underlying `BaseMutex` in the same thread is undefined behavior. If this is
unavoidable in your code, consider using `RecursiveMutex`.
-/
def Mutex.tryAtomically [Monad m] [MonadLiftT BaseIO m] [MonadFinally m]
    (mutex : Mutex α) (k : AtomicT α m β) : m (Option β) := do
  if ← mutex.mutex.tryLock then
    try
      k mutex.ref
    finally
      mutex.mutex.unlock
  else
    return none

/--
`mutex.atomicallyOnce condvar pred k` runs `k`, waiting on `condvar` until `pred` returns true.
Both `k` and `pred` have access to the mutex's state.

Calling `mutex.atomicallyOnce` while already holding the underlying `BaseMutex` in the same thread
is undefined behavior. If this is unavoidable in your code, consider using `RecursiveMutex`.
-/
def Mutex.atomicallyOnce [Monad m] [MonadLiftT BaseIO m] [MonadFinally m]
    (mutex : Mutex α) (condvar : Condvar)
    (pred : AtomicT α m Bool) (k : AtomicT α m β) : m β :=
  let _ : MonadLift BaseIO (AtomicT α m) := ⟨liftM⟩
  mutex.atomically do
    condvar.waitUntil mutex pred
    k

end Std
