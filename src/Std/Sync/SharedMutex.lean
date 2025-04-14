/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Sync.Basic

namespace Std

private opaque SharedMutexImpl : NonemptyType.{0}

/--
An exclusion primitive that allows a number of readers or at most one writer.

If you want to guard shared state, use `SharedMutex α` instead.
-/
def BaseSharedMutex : Type := SharedMutexImpl.type

instance : Nonempty BaseSharedMutex := SharedMutexImpl.property

/-- Creates a new `BaseSharedMutex`. -/
@[extern "lean_io_basesharedmutex_new"]
opaque BaseSharedMutex.new : BaseIO BaseSharedMutex

/--
Locks a `BaseSharedMutex` for exclusive write access. This function blocks until no other
writers or readers have access to the lock.

The current thread must not have already locked the mutex.
Reentrant locking is undefined behavior (inherited from the C++ implementation).
-/
@[extern "lean_io_basesharedmutex_write"]
opaque BaseSharedMutex.write (mutex : @& BaseSharedMutex) : BaseIO Unit

/--
Attempts to lock a `BaseSharedMutex` for exclusive write access. If the mutex is not available
return `false`, otherwise lock it and return `true`.

The current thread must not have already locked the mutex.
Reentrant locking is undefined behavior (inherited from the C++ implementation).
-/
@[extern "lean_io_basesharedmutex_try_write"]
opaque BaseSharedMutex.tryWrite (mutex : @& BaseSharedMutex) : BaseIO Bool

/--
Unlocks a `BaseSharedMutex` write lock.

The current thread must have already locked the mutex for write access.
Unlocking an unlocked mutex is undefined behavior (inherited from the C++ implementation).
-/
@[extern "lean_io_basesharedmutex_unlock_write"]
opaque BaseSharedMutex.unlockWrite (mutex : @& BaseSharedMutex) : BaseIO Unit

/--
Locks a `BaseSharedMutex` for shared read access. This function blocks until there are no more
writers which hold the lock. There may be other readers currently inside the lock when this method
returns.

The current thread must not have already locked the mutex.
Reentrant locking is undefined behavior (inherited from the C++ implementation).
-/
@[extern "lean_io_basesharedmutex_read"]
opaque BaseSharedMutex.read (mutex : @& BaseSharedMutex) : BaseIO Unit

/--
Attempts to lock a `BaseSharedMutex` for shared read access. If the mutex is not available
return `false`, otherwise lock it and return `true`.

The current thread must not have already locked the mutex.
Reentrant locking is undefined behavior (inherited from the C++ implementation).
-/
@[extern "lean_io_basesharedmutex_try_read"]
opaque BaseSharedMutex.tryRead (mutex : @& BaseSharedMutex) : BaseIO Bool

/--
Unlocks a `BaseSharedMutex` read lock.

The current thread must have already locked the mutex for read access.
Unlocking an unlocked mutex is undefined behavior (inherited from the C++ implementation).
-/
@[extern "lean_io_basesharedmutex_unlock_read"]
opaque BaseSharedMutex.unlockRead (mutex : @& BaseSharedMutex) : BaseIO Unit

/--
An exclusion primitive that allows a number of readers or at most one writer access to a shared
state of type `α`.
-/
structure SharedMutex (α : Type) where private mk ::
  private ref : IO.Ref α
  mutex : BaseSharedMutex
deriving Nonempty

instance : CoeOut (SharedMutex α) BaseSharedMutex where coe := SharedMutex.mutex

/-- Creates a new shared mutex. -/
def SharedMutex.new (a : α) : BaseIO (SharedMutex α) :=
  return { ref := ← IO.mkRef a, mutex := ← BaseSharedMutex.new }

/--
`mutex.atomically k` runs `k` with read and write access to the mutex's state while locking the
mutex for exclusive write access.

Calling `mutex.atomically` while already holding the underlying `BaseSharedMutex` in the same thread
is undefined behavior.
-/
def SharedMutex.atomically [Monad m] [MonadLiftT BaseIO m] [MonadFinally m]
    (mutex : SharedMutex α) (k : AtomicT α m β) : m β := do
  try
    mutex.mutex.write
    k mutex.ref
  finally
    mutex.mutex.unlockWrite

/--
`mutex.tryAtomically k` tries to lock `mutex` for exclusive write access and runs `k` with read
and write access to the mutex's state if it succeeds. If successful, it returns the value of `k`
as `some`, otherwise `none`.

Calling `mutex.tryAtomically` while already holding the underlying `BaseSharedMutex` in the same
thread is undefined behavior.
-/
def SharedMutex.tryAtomically [Monad m] [MonadLiftT BaseIO m] [MonadFinally m]
    (mutex : SharedMutex α) (k : AtomicT α m β) : m (Option β) := do
  if ← mutex.mutex.tryWrite then
    try
      k mutex.ref
    finally
      mutex.mutex.unlockWrite
  else
    return none

/--
`mutex.atomicallyRead k` runs `k` with read access to the mutex's state while locking the mutex
for shared read access.

Calling `mutex.atomicallyRead` while already holding the underlying `BaseSharedMutex` in the same
thread is undefined behavior.
-/
def SharedMutex.atomicallyRead [Monad m] [MonadLiftT BaseIO m] [MonadFinally m]
    (mutex : SharedMutex α) (k : ReaderT α m β) : m β := do
  try
    mutex.mutex.read
    let state ← (mutex.ref.get : BaseIO α)
    k state
  finally
    mutex.mutex.unlockRead

/--
`mutex.tryAtomicallyRead k` tries to lock `mutex` for shared read access and runs `k` with read
access to the mutex's state if it succeeds. If successful, it returns the value of `k`
as `some`, otherwise `none`.

Calling `mutex.tryAtomicallyRead` while already holding the underlying `BaseSharedMutex` in the
same thread is undefined behavior.
-/
def SharedMutex.tryAtomicallyRead [Monad m] [MonadLiftT BaseIO m] [MonadFinally m]
    (mutex : SharedMutex α) (k : ReaderT α m β) : m (Option β) := do
  if ← mutex.mutex.tryRead then
    try
      let state ← (mutex.ref.get : BaseIO α)
      k state
    finally
      mutex.mutex.unlockRead
  else
    return none

end Std
