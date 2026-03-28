/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
module

prelude
public import Init.System.IO

@[expose] public section

namespace Std

/--
`AtomicT α m` is the monad that can be atomically executed inside mutual exclusion primitives like
`Mutex α` with outside monad `m`. It can be seen as an atomic variant of `StateRefT`.
The action has access to the state `α` of the mutex (via `get` and `set`).
-/
def AtomicT (α : Type) (m : Type → Type) := ReaderT (IO.Ref α) m

@[inline]
nonrec def AtomicT.run [Monad m] [MonadLiftT (ST IO.RealWorld) m] (x : AtomicT α m β) (s : α) : m (β × α) := do
  let ref ← ST.mkRef s
  let result ← ReaderT.run x ref
  let state ← ref.get
  return (result, state)

@[inline]
nonrec def AtomicT.run' [Monad m] [MonadLiftT (ST IO.RealWorld) m] (x : AtomicT α m β) (s : α) : m β := do
  let ref ← ST.mkRef s
  ReaderT.run x ref

instance [Monad m] : Monad (AtomicT α m) := inferInstanceAs (Monad (ReaderT _ _))
instance : MonadLift m (AtomicT α m) := inferInstanceAs (MonadLift m (ReaderT _ _))
instance : MonadFunctor m (AtomicT α m) := inferInstanceAs (MonadFunctor m (ReaderT _ _))
instance [Alternative m] [Monad m] : Alternative (AtomicT α m) := inferInstanceAs (Alternative (ReaderT _ _))
instance [Monad m] [MonadAttach m] : MonadAttach (AtomicT α m) := inferInstanceAs (MonadAttach (ReaderT _ _))
instance : MonadControl m (AtomicT α m) := inferInstanceAs (MonadControl m (ReaderT _ _))
instance [MonadFinally m] : MonadFinally (AtomicT α m) := inferInstanceAs (MonadFinally (ReaderT _ _))
instance [MonadExceptOf ε m] : MonadExceptOf ε (AtomicT α m) := inferInstanceAs (MonadExceptOf ε (ReaderT _ _))

instance [MonadLiftT (ST IO.RealWorld) m] : MonadStateOf α (AtomicT α m) where
  get := .mk fun ref => ref.get
  set val := .mk fun ref => ref.set val
  modifyGet f := .mk fun ref => ref.modifyGet f

end Std
