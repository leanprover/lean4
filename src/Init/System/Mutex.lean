/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
prelude
import Init.System.IO
import Init.Control.StateRef


set_option linter.deprecated false

namespace IO

private opaque BaseMutexImpl : NonemptyType.{0}

/--
Mutual exclusion primitive (a lock).

If you want to guard shared state, use `Mutex α` instead.
-/
@[deprecated "Use Std.BaseMutex from Std.Sync.Mutex instead" (since := "2024-12-02")]
def BaseMutex : Type := BaseMutexImpl.type

instance : Nonempty BaseMutex := BaseMutexImpl.property

/-- Creates a new `BaseMutex`. -/
@[extern "lean_io_basemutex_new", deprecated "Use Std.BaseMutex.new from Std.Sync.Mutex instead" (since := "2024-12-02")]
opaque BaseMutex.new : BaseIO BaseMutex

/--
Locks a `BaseMutex`.  Waits until no other thread has locked the mutex.

The current thread must not have already locked the mutex.
Reentrant locking is undefined behavior (inherited from the C++ implementation).
-/
@[extern "lean_io_basemutex_lock", deprecated "Use Std.BaseMutex.lock from Std.Sync.Mutex instead" (since := "2024-12-02")]
opaque BaseMutex.lock (mutex : @& BaseMutex) : BaseIO Unit

/--
Unlocks a `BaseMutex`.

The current thread must have already locked the mutex.
Unlocking an unlocked mutex is undefined behavior (inherited from the C++ implementation).
-/
@[extern "lean_io_basemutex_unlock", deprecated "Use Std.BaseMutex.unlock from Std.Sync.Mutex instead" (since := "2024-12-02")]
opaque BaseMutex.unlock (mutex : @& BaseMutex) : BaseIO Unit

private opaque CondvarImpl : NonemptyType.{0}

/-- Condition variable. -/
@[deprecated "Use Std.Condvar from Std.Sync.Mutex instead" (since := "2024-12-02")]
def Condvar : Type := CondvarImpl.type

instance : Nonempty Condvar := CondvarImpl.property

/-- Creates a new condition variable. -/
@[extern "lean_io_condvar_new", deprecated "Use Std.Condvar.new from Std.Sync.Mutex instead" (since := "2024-12-02")]
opaque Condvar.new : BaseIO Condvar

/-- Waits until another thread calls `notifyOne` or `notifyAll`. -/
@[extern "lean_io_condvar_wait", deprecated "Use Std.Condvar.wait from Std.Sync.Mutex instead" (since := "2024-12-02")]
opaque Condvar.wait (condvar : @& Condvar) (mutex : @& BaseMutex) : BaseIO Unit

/-- Wakes up a single other thread executing `wait`. -/
@[extern "lean_io_condvar_notify_one", deprecated "Use Std.Condvar.notifyOne from Std.Sync.Mutex instead" (since := "2024-12-02")]
opaque Condvar.notifyOne (condvar : @& Condvar) : BaseIO Unit

/-- Wakes up all other threads executing `wait`. -/
@[extern "lean_io_condvar_notify_all", deprecated "Use Std.Condvar.notifyAll from Std.Sync.Mutex instead" (since := "2024-12-02")]
opaque Condvar.notifyAll (condvar : @& Condvar) : BaseIO Unit

/-- Waits on the condition variable until the predicate is true. -/
@[deprecated "Use Std.Condvar.waitUntil from Std.Sync.Mutex instead" (since := "2024-12-02")]
def Condvar.waitUntil [Monad m] [MonadLift BaseIO m]
    (condvar : Condvar) (mutex : BaseMutex) (pred : m Bool) : m Unit := do
  while !(← pred) do
    condvar.wait mutex

/--
Mutual exclusion primitive (lock) guarding shared state of type `α`.

The type `Mutex α` is similar to `IO.Ref α`,
except that concurrent accesses are guarded by a mutex
instead of atomic pointer operations and busy-waiting.
-/
@[deprecated "Use Std.Mutex from Std.Sync.Mutex instead" (since := "2024-12-02")]
structure Mutex (α : Type) where private mk ::
  private ref : IO.Ref α
  mutex : BaseMutex
  deriving Nonempty

instance : CoeOut (Mutex α) BaseMutex where coe := Mutex.mutex

/-- Creates a new mutex. -/
@[deprecated "Use Std.Mutex.new from Std.Sync.Mutex instead" (since := "2024-12-02")]
def Mutex.new (a : α) : BaseIO (Mutex α) :=
  return { ref := ← mkRef a, mutex := ← BaseMutex.new }

/--
`AtomicT α m` is the monad that can be atomically executed inside a `Mutex α`,
with outside monad `m`.
The action has access to the state `α` of the mutex (via `get` and `set`).
-/
@[deprecated "Use Std.AtomicT from Std.Sync.Mutex instead" (since := "2024-12-02")]
abbrev AtomicT := StateRefT' IO.RealWorld

/-- `mutex.atomically k` runs `k` with access to the mutex's state while locking the mutex. -/
@[deprecated "Use Std.Mutex.atomically from Std.Sync.Mutex instead" (since := "2024-12-02")]
def Mutex.atomically [Monad m] [MonadLiftT BaseIO m] [MonadFinally m]
    (mutex : Mutex α) (k : AtomicT α m β) : m β := do
  try
    mutex.mutex.lock
    k mutex.ref
  finally
    mutex.mutex.unlock

/--
`mutex.atomicallyOnce condvar pred k` runs `k`,
waiting on `condvar` until `pred` returns true.
Both `k` and `pred` have access to the mutex's state.
-/
@[deprecated "Use Std.Mutex.atomicallyOnce from Std.Sync.Mutex instead" (since := "2024-12-02")]
def Mutex.atomicallyOnce [Monad m] [MonadLiftT BaseIO m] [MonadFinally m]
    (mutex : Mutex α) (condvar : Condvar)
    (pred : AtomicT α m Bool) (k : AtomicT α m β) : m β :=
  let _ : MonadLift BaseIO (AtomicT α m) := ⟨liftM⟩
  mutex.atomically do
    condvar.waitUntil mutex pred
    k
