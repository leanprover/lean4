/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.Family

namespace Lake

/-- A monad equipped with a dependently typed key-value store for a particular key. -/
class MonadStore1 {κ : Type u} (k : κ) (α : semiOutParam $ Type v) (m : Type v → Type w) where
  fetch? : m (Option α)
  store : α → m PUnit

export MonadStore1 (fetch? store)

/-- A monad equipped with a dependently typed key-object store. -/
class MonadDStore (κ : Type u) (β : semiOutParam $ κ → Type v) (m : Type v → Type w) where
  fetch? : (key : κ) → m (Option (β key))
  store : (key : κ) → β key → m PUnit

/-- A monad equipped with a key-object store. -/
abbrev MonadStore κ α m := MonadDStore κ (fun _ => α) m

@[inline] instance [MonadDStore κ β m] [t : FamilyOut β k α] : MonadStore1 k α m where
  fetch? := t.family_key_eq_type ▸ MonadDStore.fetch? k
  store a := MonadDStore.store k <| cast t.family_key_eq_type.symm a

instance [MonadLift m n] [MonadDStore κ β m] : MonadDStore κ β n where
  fetch? k := liftM (m := m) <| MonadDStore.fetch? k
  store k a := liftM (m := m) <| MonadDStore.store k a

@[inline] def fetchOrCreate [Monad m]
(key : κ) [MonadStore1 key α m] (create : m α) : m α := do
  if let some val ← fetch? key then
    return val
  else
    let val ← create
    store key val
    return val
