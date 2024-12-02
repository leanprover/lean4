/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Init.Notation

namespace Lake

/-- A monad equipped with a dependently typed key-value store for a particular key. -/
class MonadStore1Of {κ : Type u} (k : κ) (α : semiOutParam $ Type v) (m : Type v → Type w) where
  fetch? : m (Option α)
  store : α → m PUnit

export MonadStore1Of (store)

/-- Similar to `MonadStore1Of`, but `α` is an `outParam` for convenience. -/
class MonadStore1 {κ : Type u} (k : κ) (α : outParam $ Type v) (m : Type v → Type w) where
  fetch? : m (Option α)
  store : α → m PUnit

export MonadStore1 (fetch?)

instance [MonadStore1Of k α m] : MonadStore1 k α m where
  fetch? := MonadStore1Of.fetch? k
  store := MonadStore1Of.store k

/-- A monad equipped with a dependently typed key-object store. -/
class MonadDStore (κ : Type u) (β : semiOutParam $ κ → Type v) (m : Type v → Type w) where
  fetch? : (key : κ) → m (Option (β key))
  store : (key : κ) → β key → m PUnit

instance [MonadDStore κ β m] : MonadStore1Of k (β k) m where
  fetch? := MonadDStore.fetch? k
  store o := MonadDStore.store k o

/-- A monad equipped with a key-object store. -/
abbrev MonadStore κ α m := MonadDStore κ (fun _ => α) m

instance [MonadLift m n] [MonadDStore κ β m] : MonadDStore κ β n where
  fetch? k := liftM (m := m) <| fetch? k
  store k a := liftM (m := m) <| store k a

@[inline] def fetchOrCreate [Monad m]
(key : κ) [MonadStore1Of key α m] (create : m α) : m α := do
  if let some val ← fetch? key then
    return val
  else
    let val ← create
    store key val
    return val
