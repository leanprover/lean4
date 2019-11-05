/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Control.Reader
import Init.Control.EState
import Init.Data.HashMap

namespace Lean
/-- Interface for caching results.  -/
class MonadCache (α β : Type) (m : Type → Type) :=
(findCached {} : α → m (Option β))
(cache      {} : α → β → m Unit)

/-- If entry `a := b` is already in the cache, then return `b`.
    Otherwise, execute `b ← f a`, store `a := b` in the cache and return `b`. -/
@[inline] def checkCache {α β : Type} {m : Type → Type} [MonadCache α β m] [Monad m] (a : α) (f : α → m β) : m β :=
do optB ← MonadCache.findCached a;
   match optB with
   | some b => pure b
   | none   => do
     b ← f a;
     MonadCache.cache a b;
     pure b

instance readerLift {α β ρ : Type} {m : Type → Type} [MonadCache α β m] : MonadCache α β (ReaderT ρ m) :=
{ findCached := fun a r   => MonadCache.findCached a,
  cache      := fun a b r => MonadCache.cache a b }

instance exceptLift {α β ε : Type} {m : Type → Type} [MonadCache α β m] [Monad m] : MonadCache α β (ExceptT ε m) :=
{ findCached := fun a   => ExceptT.lift $ MonadCache.findCached a,
  cache      := fun a b => ExceptT.lift $ MonadCache.cache a b }

/-- Adapter for implementing `MonadCache` interface using `HashMap`s.
    We just have to specify how to extract/modify the `HashMap`. -/
class MonadHashMapCacheAdapter (α β : Type) (m : Type → Type) [HasBeq α] [Hashable α] :=
(getCache {}    : m (HashMap α β))
(modifyCache {} : (HashMap α β → HashMap α β) → m Unit)

namespace MonadHashMapCacheAdapter

@[inline] def findCached {α β : Type} {m : Type → Type} [HasBeq α] [Hashable α] [Monad m] [MonadHashMapCacheAdapter α β m] (a : α) : m (Option β) :=
do c ← getCache;
   pure (c.find a)

@[inline] def cache {α β : Type} {m : Type → Type} [HasBeq α] [Hashable α] [MonadHashMapCacheAdapter α β m] (a : α) (b : β) : m Unit :=
modifyCache $ fun s => s.insert a b

instance {α β : Type} {m : Type → Type} [HasBeq α] [Hashable α] [Monad m] [MonadHashMapCacheAdapter α β m] : MonadCache α β m :=
{ findCached := MonadHashMapCacheAdapter.findCached,
  cache      := MonadHashMapCacheAdapter.cache }

end MonadHashMapCacheAdapter

/-- Auxiliary structure for "adding" a `HashMap` to a state object. -/
structure WithHashMapCache (α β σ : Type) [HasBeq α] [Hashable α] :=
(state : σ)
(cache : HashMap α β := {})

namespace WithHashMapCache

@[inline] def getCache {α β σ : Type} [HasBeq α] [Hashable α] : StateM (WithHashMapCache α β σ) (HashMap α β) :=
do s ← get; pure s.cache

@[inline] def modifyCache {α β σ : Type} [HasBeq α] [Hashable α] (f : HashMap α β → HashMap α β) : StateM (WithHashMapCache α β σ) Unit :=
modify $ fun s => { cache := f s.cache, .. s }

instance stateAdapter (α β σ : Type) [HasBeq α] [Hashable α] : MonadHashMapCacheAdapter α β (StateM (WithHashMapCache α β σ)) :=
{ getCache    := WithHashMapCache.getCache,
  modifyCache := WithHashMapCache.modifyCache }

@[inline] def getCacheE {α β ε σ : Type} [HasBeq α] [Hashable α] : EStateM ε (WithHashMapCache α β σ) (HashMap α β) :=
do s ← get; pure s.cache

@[inline] def modifyCacheE {α β ε σ : Type} [HasBeq α] [Hashable α] (f : HashMap α β → HashMap α β) : EStateM ε (WithHashMapCache α β σ) Unit :=
modify $ fun s => { cache := f s.cache, .. s }

instance estateAdapter (α β ε σ : Type) [HasBeq α] [Hashable α] : MonadHashMapCacheAdapter α β (EStateM ε (WithHashMapCache α β σ)) :=
{ getCache    := WithHashMapCache.getCacheE,
  modifyCache := WithHashMapCache.modifyCacheE }

@[inline] def fromState {α β σ δ : Type} [HasBeq α] [Hashable α] (x : StateM σ δ) : StateM (WithHashMapCache α β σ) δ :=
adaptState
  (fun (s : WithHashMapCache α β σ)  => (s.state, s.cache))
  (fun (s : σ) (cache : HashMap α β) => { state := s, cache := cache })
  x

@[inline] def toState {α β σ δ : Type} [HasBeq α] [Hashable α] (x : StateM (WithHashMapCache α β σ) δ) : StateM σ δ :=
adaptState'
  (fun (s : σ) => ({ state := s } : WithHashMapCache α β σ))
  (fun (s : WithHashMapCache α β σ) => s.state)
  x

@[inline] def fromEState {α β σ ε δ : Type} [HasBeq α] [Hashable α] (x : EStateM ε σ δ) : EStateM ε (WithHashMapCache α β σ) δ :=
adaptState
  (fun (s : WithHashMapCache α β σ)  => (s.state, s.cache))
  (fun (s : σ) (cache : HashMap α β) => { state := s, cache := cache })
  x

@[inline] def toEState {α β σ ε δ : Type} [HasBeq α] [Hashable α] (x : EStateM ε (WithHashMapCache α β σ) δ) : EStateM ε σ δ :=
adaptState'
  (fun (s : σ) => ({ state := s } : WithHashMapCache α β σ))
  (fun (s : WithHashMapCache α β σ) => s.state)
  x

end WithHashMapCache
end Lean
