/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
namespace Lake

/-- A monad equipped with a dependently typed key-value store for a particular key. -/
class MonadStore1 {κ : Type u} (k : κ) (α : outParam $ Type v) (m : Type v → Type w) where
  fetch? : m (Option α)
  store : α → m PUnit

export MonadStore1 (fetch? store)

/-- A monad equipped with a dependently typed key-object store. -/
class MonadDStore (κ : Type u) (β : outParam $ κ → Type v) (m : Type v → Type w) where
  fetch? : (key : κ) → m (Option (β key))
  store : (key : κ) → β key → m PUnit

instance [MonadDStore κ β m] : MonadStore1 k (β k) m where
  fetch? := MonadDStore.fetch? k
  store o := MonadDStore.store k o

/-- A monad equipped with a key-object store. -/
abbrev MonadStore κ α m := MonadDStore κ (fun _ => α) m

instance [MonadLift m n] [MonadDStore κ β m] : MonadDStore κ β n where
  fetch? k := liftM (m := m) <| fetch? k
  store k a := liftM (m := m) <| store k a

@[inline] def fetchOrCreate [Monad m]
(key : κ) [MonadStore1 key α m] (create : m α) : m α := do
  if let some val ← fetch? key then
    return val
  else
    let val ← create
    store key val
    return val
