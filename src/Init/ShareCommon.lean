/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
prelude
import Init.Util
import Init.Data.UInt.Basic

namespace ShareCommon
/-
  The max sharing primitives are implemented internally.
  They use maps and sets of Lean objects. We have two versions:
  one using `HashMap` and `HashSet`, and another using
  `PersistentHashMap` and `PersistentHashSet`.
  These maps and sets are "instantiated here using the "unsafe"
  primitives `Object.eq`, `Object.hash`, and `ptrAddrUnsafe`. -/
abbrev Object : Type := NonScalar

unsafe def Object.ptrEq (a b : Object) : Bool :=
  ptrAddrUnsafe a == ptrAddrUnsafe b

unsafe abbrev Object.ptrHash (a : Object) : UInt64 :=
  ptrAddrUnsafe a |>.toUInt64

structure StateFactoryImpl where
  (Map Set : Type)
  mkState : Unit → Map × Set
  mapFind? (m : Map) (k : Object) : Option Object
  mapInsert (m : Map) (k v : Object) : Map
  setFind? (m : Set) (k : Object) : Option Object
  setInsert (m : Set) (o : Object) : Set

opaque StateFactoryPointed : NonemptyType
abbrev StateFactory : Type := StateFactoryPointed.type
instance : Nonempty StateFactory := StateFactoryPointed.property

@[extern "lean_sharecommon_eq"]
unsafe opaque Object.eq (a b : @& Object) : Bool

@[extern "lean_sharecommon_hash"]
unsafe opaque Object.hash (a : @& Object) : UInt64

structure StateFactoryBuilder where
  Map (α _β : Type) [BEq α] [Hashable α] : Type
  mkMap {α β : Type} [BEq α] [Hashable α] (capacity : Nat) : Map α β
  mapFind? {α β : Type} [BEq α] [Hashable α] : Map α β → α → Option β
  mapInsert {α β : Type} [BEq α] [Hashable α] : Map α β → α → β → Map α β
  Set (α : Type) [BEq α] [Hashable α] : Type
  mkSet {α : Type} [BEq α] [Hashable α] (capacity : Nat) : Set α
  setFind? {α : Type} [BEq α] [Hashable α] : Set α → α → Option α
  setInsert {α : Type} [BEq α] [Hashable α] : Set α → α → Set α

unsafe def StateFactory.mkImpl : StateFactoryBuilder → StateFactory
  | { Map, mkMap, mapFind?, mapInsert, Set, mkSet, setFind?, setInsert } =>
    unsafeCast {
      Map := @Map Object Object ⟨Object.ptrEq⟩ ⟨Object.ptrHash⟩
      Set := @Set Object ⟨Object.eq⟩ ⟨Object.hash⟩
      mkState := fun _ => (
        @mkMap Object Object ⟨Object.ptrEq⟩ ⟨Object.ptrHash⟩ 1024,
        @mkSet Object ⟨Object.eq⟩ ⟨Object.hash⟩ 1024)
      mapFind? := @mapFind? Object Object ⟨Object.ptrEq⟩ ⟨Object.ptrHash⟩
      mapInsert := @mapInsert Object Object ⟨Object.ptrEq⟩ ⟨Object.ptrHash⟩
      setFind? := @setFind? Object ⟨Object.eq⟩ ⟨Object.hash⟩
      setInsert := @setInsert Object ⟨Object.eq⟩ ⟨Object.hash⟩
    : StateFactoryImpl }

@[implemented_by StateFactory.mkImpl]
opaque StateFactory.mk : StateFactoryBuilder → StateFactory

unsafe def StateFactory.get : StateFactory → StateFactoryImpl := unsafeCast

/-- Internally `State` is implemented as a pair `ObjectMap` and `ObjectSet` -/
opaque StatePointed (σ : StateFactory) : NonemptyType
abbrev State (σ : StateFactory) : Type u := (StatePointed σ).type
instance : Nonempty (State σ) := (StatePointed σ).property

unsafe def mkStateImpl (σ : StateFactory) : State σ := unsafeCast (σ.get.mkState ())
@[implemented_by mkStateImpl] opaque State.mk (σ : StateFactory) : State σ
instance : Inhabited (State σ) := ⟨.mk σ⟩

@[extern "lean_state_sharecommon"]
def State.shareCommon {σ : @& StateFactory} (s : State σ) (a : α) : α × State σ := (a, s)

end ShareCommon

class MonadShareCommon (m : Type u → Type v) where
  withShareCommon {α : Type u} : α → m α

abbrev withShareCommon := @MonadShareCommon.withShareCommon

abbrev shareCommonM [MonadShareCommon m] (a : α) : m α :=
  withShareCommon a

abbrev ShareCommonT (σ) (m : Type u → Type v) := StateT (ShareCommon.State σ) m
abbrev ShareCommonM (σ) := ShareCommonT σ Id

@[specialize] def ShareCommonT.withShareCommon [Monad m] (a : α) : ShareCommonT σ m α :=
  modifyGet fun s => s.shareCommon a

instance ShareCommonT.monadShareCommon [Monad m] : MonadShareCommon (ShareCommonT σ m) where
  withShareCommon := ShareCommonT.withShareCommon

@[inline] def ShareCommonT.run [Monad m] (x : ShareCommonT σ m α) : m α := x.run' default
@[inline] def ShareCommonM.run (x : ShareCommonM σ α) : α := ShareCommonT.run x

/--
A more restrictive but efficient max sharing primitive.

Remark: it optimizes the number of RC operations, and the strategy for caching results.
-/
@[extern "lean_sharecommon_quick"]
def ShareCommon.shareCommon' (a : @& α) : α := a
