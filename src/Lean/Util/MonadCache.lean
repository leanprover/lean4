/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Control.StateRef
import Lean.Data.HashMap
import Std.Data.HashMap.Basic

namespace Lean
/-- Interface for caching results.  -/
class MonadCache (α β : Type) (m : Type → Type) where
  findCached? : α → m (Option β)
  cache       : α → β → m Unit

/-- If entry `a := b` is already in the cache, then return `b`.
    Otherwise, execute `b ← f ()`, store `a := b` in the cache and return `b`. -/
@[always_inline, inline]
def checkCache {α β : Type} {m : Type → Type} [MonadCache α β m] [Monad m] (a : α) (f : Unit → m β) : m β := do
  match (← MonadCache.findCached? a) with
  | some b => pure b
  | none   => do
    let b ← f ()
    MonadCache.cache a b
    pure b

instance {α β ρ : Type} {m : Type → Type} [MonadCache α β m] : MonadCache α β (ReaderT ρ m) where
  findCached? a _ := MonadCache.findCached? a
  cache a b _ := MonadCache.cache a b

@[always_inline]
instance {α β ε : Type} {m : Type → Type} [MonadCache α β m] [Monad m] : MonadCache α β (ExceptT ε m) where
  findCached? a := ExceptT.lift $ MonadCache.findCached? a
  cache a b := ExceptT.lift $ MonadCache.cache a b

/-- Adapter for implementing `MonadCache` interface using `HashMap`s.
    We just have to specify how to extract/modify the `HashMap`. -/
class MonadHashMapCacheAdapter (α β : Type) (m : Type → Type) [BEq α] [Hashable α] where
  getCache    : m (Std.HashMap α β)
  modifyCache : (Std.HashMap α β → Std.HashMap α β) → m Unit

namespace MonadHashMapCacheAdapter

@[always_inline, inline]
def findCached? {α β : Type} {m : Type → Type} [BEq α] [Hashable α] [Monad m] [MonadHashMapCacheAdapter α β m] (a : α) : m (Option β) := do
  let c ← getCache
  pure (c.get? a)

@[always_inline, inline]
def cache {α β : Type} {m : Type → Type} [BEq α] [Hashable α] [MonadHashMapCacheAdapter α β m] (a : α) (b : β) : m Unit :=
  modifyCache fun s => s.insert a b

instance {α β : Type} {m : Type → Type} [BEq α] [Hashable α] [Monad m] [MonadHashMapCacheAdapter α β m] : MonadCache α β m where
  findCached? := MonadHashMapCacheAdapter.findCached?
  cache       := MonadHashMapCacheAdapter.cache

end MonadHashMapCacheAdapter

def MonadCacheT {ω} (α β : Type) (m : Type → Type) [STWorld ω m] [BEq α] [Hashable α] := StateRefT (Std.HashMap α β) m

namespace MonadCacheT

variable {ω α β : Type} {m : Type → Type} [STWorld ω m] [BEq α] [Hashable α] [MonadLiftT (ST ω) m] [Monad m]

instance  : MonadHashMapCacheAdapter α β (MonadCacheT α β m) where
  getCache := (get : StateRefT' ..)
  modifyCache f := (modify f : StateRefT' ..)

@[inline] def run {σ} (x : MonadCacheT α β m σ) : m σ :=
  x.run' Std.HashMap.empty

instance : Monad (MonadCacheT α β m) := inferInstanceAs (Monad (StateRefT' _ _ _))
instance : MonadLift m (MonadCacheT α β m) := inferInstanceAs (MonadLift m (StateRefT' _ _ _))
instance (ε) [MonadExceptOf ε m] : MonadExceptOf ε (MonadCacheT α β m) := inferInstanceAs (MonadExceptOf ε (StateRefT' _ _ _))
instance : MonadControl m (MonadCacheT α β m) := inferInstanceAs (MonadControl m (StateRefT' _ _ _))
instance [MonadFinally m] : MonadFinally (MonadCacheT α β m) := inferInstanceAs (MonadFinally (StateRefT' _ _ _))
instance [MonadRef m] : MonadRef (MonadCacheT α β m) := inferInstanceAs (MonadRef (StateRefT' _ _ _))
instance [Alternative m] : Alternative (MonadCacheT α β m) := inferInstanceAs (Alternative (StateRefT' _ _ _))

end MonadCacheT

/- Similar to `MonadCacheT`, but using `StateT` instead of `StateRefT` -/
def MonadStateCacheT (α β : Type) (m : Type → Type) [BEq α] [Hashable α] := StateT (Std.HashMap α β) m

namespace MonadStateCacheT

variable {ω α β : Type} {m : Type → Type} [STWorld ω m] [BEq α] [Hashable α] [MonadLiftT (ST ω) m] [Monad m]

instance  : MonadHashMapCacheAdapter α β (MonadStateCacheT α β m) where
  getCache := (get : StateT ..)
  modifyCache f := (modify f : StateT ..)

@[always_inline, inline] def run {σ} (x : MonadStateCacheT α β m σ) : m σ :=
  x.run' Std.HashMap.empty

instance : Monad (MonadStateCacheT α β m) := inferInstanceAs (Monad (StateT _ _))
instance : MonadLift m (MonadStateCacheT α β m) := inferInstanceAs (MonadLift m (StateT _ _))
instance (ε) [MonadExceptOf ε m] : MonadExceptOf ε (MonadStateCacheT α β m) := inferInstanceAs (MonadExceptOf ε (StateT _ _))
instance : MonadControl m (MonadStateCacheT α β m) := inferInstanceAs (MonadControl m (StateT _ _))
instance [MonadFinally m] : MonadFinally (MonadStateCacheT α β m) := inferInstanceAs (MonadFinally (StateT _ _))
instance [MonadRef m] : MonadRef (MonadStateCacheT α β m) := inferInstanceAs (MonadRef (StateT _ _))

end MonadStateCacheT

end Lean
