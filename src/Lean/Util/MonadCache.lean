/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Std.Data.HashMap

namespace Lean
/-- Interface for caching results.  -/
class MonadCache (α β : Type) (m : Type → Type) where
  findCached? : α → m (Option β)
  cache       : α → β → m Unit

/-- If entry `a := b` is already in the cache, then return `b`.
    Otherwise, execute `b ← f a`, store `a := b` in the cache and return `b`. -/
@[inline] def checkCache {α β : Type} {m : Type → Type} [MonadCache α β m] [Monad m] (a : α) (f : Unit → m β) : m β := do
match (← MonadCache.findCached? a) with
  | some b => pure b
  | none   => do
    let b ← f ()
    MonadCache.cache a b
    pure b

instance {α β ρ : Type} {m : Type → Type} [MonadCache α β m] : MonadCache α β (ReaderT ρ m) := {
  findCached? := fun a r   => MonadCache.findCached? a,
  cache       := fun a b r => MonadCache.cache a b
}

instance {α β ε : Type} {m : Type → Type} [MonadCache α β m] [Monad m] : MonadCache α β (ExceptT ε m) := {
  findCached? := fun a   => ExceptT.lift $ MonadCache.findCached? a,
  cache       := fun a b => ExceptT.lift $ MonadCache.cache a b
}

open Std (HashMap)

/-- Adapter for implementing `MonadCache` interface using `HashMap`s.
    We just have to specify how to extract/modify the `HashMap`. -/
class MonadHashMapCacheAdapter (α β : Type) (m : Type → Type) [BEq α] [Hashable α] where
  getCache    : m (HashMap α β)
  modifyCache : (HashMap α β → HashMap α β) → m Unit

namespace MonadHashMapCacheAdapter

@[inline] def findCached? {α β : Type} {m : Type → Type} [BEq α] [Hashable α] [Monad m] [MonadHashMapCacheAdapter α β m] (a : α) : m (Option β) := do
  let c ← getCache
  pure (c.find? a)

@[inline] def cache {α β : Type} {m : Type → Type} [BEq α] [Hashable α] [MonadHashMapCacheAdapter α β m] (a : α) (b : β) : m Unit :=
  modifyCache fun s => s.insert a b

instance {α β : Type} {m : Type → Type} [BEq α] [Hashable α] [Monad m] [MonadHashMapCacheAdapter α β m] : MonadCache α β m := {
  findCached? := MonadHashMapCacheAdapter.findCached?,
  cache       := MonadHashMapCacheAdapter.cache
}

end MonadHashMapCacheAdapter

def MonadCacheT {ω} (α β : Type) (m : Type → Type) [STWorld ω m] [BEq α] [Hashable α] := StateRefT (HashMap α β) m

namespace MonadCacheT

variables {ω α β : Type} {m : Type → Type} [STWorld ω m] [BEq α] [Hashable α] [MonadLiftT (ST ω) m] [Monad m]

instance  : MonadHashMapCacheAdapter α β (MonadCacheT α β m) := {
  getCache    := (get : StateRefT' ..),
  modifyCache := fun f => (modify f : StateRefT' ..)
}

@[inline] def run {σ} (x : MonadCacheT α β m σ) : m σ :=
  x.run' Std.mkHashMap

instance : Monad (MonadCacheT α β m) := inferInstanceAs (Monad (StateRefT' _ _ _))
instance : MonadLift m (MonadCacheT α β m) := inferInstanceAs (MonadLift m (StateRefT' _ _ _))
instance (ε) [MonadExceptOf ε m] : MonadExceptOf ε (MonadCacheT α β m) := inferInstanceAs (MonadExceptOf ε (StateRefT' _ _ _))
instance : MonadControl m (MonadCacheT α β m) := inferInstanceAs (MonadControl m (StateRefT' _ _ _))
instance [MonadFinally m] : MonadFinally (MonadCacheT α β m) := inferInstanceAs (MonadFinally (StateRefT' _ _ _))
instance [MonadRef m] : MonadRef (MonadCacheT α β m) := inferInstanceAs (MonadRef (StateRefT' _ _ _))

end MonadCacheT
end Lean
