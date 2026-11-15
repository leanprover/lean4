/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Init.Notation

set_option doc.verso true

namespace Lake

/-- A monad equipped with a dependently typed key-value store for a particular key. -/
public class MonadStore1Of {κ : Type u} (k : κ) (α : semiOutParam (Type v)) (m : Type v → Type w) where
  fetch? : m (Option α)
  store : α → m PUnit

export MonadStore1Of (store)

/-- Similar to {lean}`MonadStore1Of`, but {lean}`α` is an {lean}`outParam` for convenience. -/
public class MonadStore1 {κ : Type u} (k : κ) (α : outParam (Type v)) (m : Type v → Type w) where
  fetch? : m (Option α)
  store : α → m PUnit

export MonadStore1 (fetch?)

public instance [MonadStore1Of k α m] : MonadStore1 k α m where
  fetch? := MonadStore1Of.fetch? k
  store := MonadStore1Of.store k

/-- A monad equipped with a dependently typed key-object store. -/
public class MonadDStore (κ : Type u) (β : semiOutParam (κ → Type v)) (m : Type v → Type w) where
  fetch? : (key : κ) → m (Option (β key))
  store : (key : κ) → β key → m PUnit

public instance [MonadDStore κ β m] : MonadStore1Of k (β k) m where
  fetch? := MonadDStore.fetch? k
  store o := MonadDStore.store k o

/-- A monad equipped with a key-object store. -/
public abbrev MonadStore κ α m := MonadDStore κ (fun _ => α) m

public instance [MonadLift m n] [MonadDStore κ β m] : MonadDStore κ β n where
  fetch? k := liftM (m := m) (fetch? k)
  store k a := liftM (m := m) (store k a)

/--
Returns the value of {lean}`key` in the store if it exists.
Otherwise, runs {lean}`create` to generate it, adds it to the store, and returns the result.

**Note:** This implementation does not update the store atomically.
-/
@[inline] public def fetchOrCreateNonatomic
  [Monad m] (key : κ) [MonadStore1Of key α m] (create : m α)
: m α := do
  if let some val ← fetch? key then
    return val
  else
    let val ← create
    store key val
    return val

@[inherit_doc fetchOrCreateNonatomic, deprecated fetchOrCreateNonatomic (since := "2026-11-14")]
public abbrev fetchOrCreate := @fetchOrCreateNonatomic
