/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Bootstrap.Data.HashSet
import Bootstrap.Data.HashMap
import Bootstrap.Data.PersistentHashMap
import Bootstrap.Data.PersistentHashSet
namespace Std
universe u v

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

unsafe def StateFactory.mk : StateFactoryImpl → StateFactory := unsafeCast
unsafe def StateFactory.get : StateFactory → StateFactoryImpl := unsafeCast

@[extern "lean_sharecommon_eq"]
unsafe opaque Object.eq (a b : @& Object) : Bool

@[extern "lean_sharecommon_hash"]
unsafe opaque Object.hash (a : @& Object) : UInt64

unsafe def objectFactoryImpl : StateFactory :=
  StateFactory.mk {
    Map := @HashMap Object Object ⟨Object.ptrEq⟩ ⟨Object.ptrHash⟩
    Set := @HashSet Object ⟨Object.eq⟩ ⟨Object.hash⟩
    mkState := fun _ => (
      @mkHashMap Object Object ⟨Object.ptrEq⟩ ⟨Object.ptrHash⟩ 1024,
      @mkHashSet Object ⟨Object.eq⟩ ⟨Object.hash⟩ 1024)
    mapFind? := @HashMap.find? Object Object ⟨Object.ptrEq⟩ ⟨Object.ptrHash⟩
    mapInsert := @HashMap.insert Object Object ⟨Object.ptrEq⟩ ⟨Object.ptrHash⟩
    setFind? := @HashSet.find? Object ⟨Object.eq⟩ ⟨Object.hash⟩
    setInsert := @HashSet.insert Object ⟨Object.eq⟩ ⟨Object.hash⟩
  }
@[implementedBy objectFactoryImpl] opaque objectFactory : StateFactory

unsafe def persistentObjectFactoryImpl : StateFactory :=
  StateFactory.mk {
    Map := @PersistentHashMap Object Object ⟨Object.ptrEq⟩ ⟨Object.ptrHash⟩
    Set := @PersistentHashSet Object ⟨Object.eq⟩ ⟨Object.hash⟩
    mkState := fun _ => (
      @PersistentHashMap.empty Object Object ⟨Object.ptrEq⟩ ⟨Object.ptrHash⟩,
      @PersistentHashSet.empty Object ⟨Object.eq⟩ ⟨Object.hash⟩)
    mapFind? := @PersistentHashMap.find? Object Object ⟨Object.ptrEq⟩ ⟨Object.ptrHash⟩
    mapInsert := @PersistentHashMap.insert Object Object ⟨Object.ptrEq⟩ ⟨Object.ptrHash⟩
    setFind? := @PersistentHashSet.find? Object ⟨Object.eq⟩ ⟨Object.hash⟩
    setInsert := @PersistentHashSet.insert Object ⟨Object.eq⟩ ⟨Object.hash⟩
  }
@[implementedBy persistentObjectFactoryImpl] opaque persistentObjectFactory : StateFactory

/-- Internally `State` is implemented as a pair `ObjectMap` and `ObjectSet` -/
opaque StatePointed (σ : StateFactory) : NonemptyType
abbrev State (σ : StateFactory) : Type u := (StatePointed σ).type
instance : Nonempty (State σ) := (StatePointed σ).property

unsafe def mkStateImpl (σ : StateFactory) : State σ := unsafeCast (σ.get.mkState ())
@[implementedBy mkStateImpl] opaque mkState (σ : StateFactory) : State σ

@[extern "lean_state_sharecommon"]
def State.shareCommon {σ : @& StateFactory} (s : State σ) (a : α) : α × State σ := (a, s)

end ShareCommon

class MonadShareCommon (m : Type u → Type v) where
  withShareCommon {α : Type u} : α → m α

abbrev withShareCommon := @MonadShareCommon.withShareCommon

abbrev shareCommonM [MonadShareCommon m] (a : α) : m α :=
  withShareCommon a

abbrev GShareCommonT (σ) (m : Type u → Type v) := StateT (ShareCommon.State σ) m
abbrev GShareCommonM (σ) := GShareCommonT σ Id
abbrev ShareCommonT := GShareCommonT ShareCommon.objectFactory
abbrev PShareCommonT := GShareCommonT ShareCommon.persistentObjectFactory
abbrev ShareCommonM := ShareCommonT Id
abbrev PShareCommonM := PShareCommonT Id

@[specialize] def GShareCommonT.withShareCommon [Monad m] (a : α) : GShareCommonT σ m α :=
  modifyGet fun s => s.shareCommon a

@[specialize] def ShareCommonT.withShareCommon [Monad m] (a : α) : ShareCommonT m α :=
  modifyGet fun s => s.shareCommon a

@[specialize] def PShareCommonT.withShareCommon [Monad m] (a : α) : PShareCommonT m α :=
  modifyGet fun s => s.shareCommon a

instance ShareCommonT.monadShareCommon [Monad m] : MonadShareCommon (ShareCommonT m) := {
  withShareCommon := ShareCommonT.withShareCommon
}

instance PShareCommonT.monadShareCommon [Monad m] : MonadShareCommon (PShareCommonT m) := {
  withShareCommon := PShareCommonT.withShareCommon
}

@[inline] def GShareCommonT.run [Monad m] (x : GShareCommonT σ m α) : m α :=
  x.run' (ShareCommon.mkState σ)

@[inline] def ShareCommonT.run [Monad m] (x : ShareCommonT m α) : m α := GShareCommonT.run x
@[inline] def PShareCommonT.run [Monad m] (x : PShareCommonT m α) : m α := GShareCommonT.run x

@[inline] def GShareCommonM.run (x : GShareCommonM σ α) : α := GShareCommonT.run x
@[inline] def ShareCommonM.run (x : ShareCommonM α) : α := ShareCommonT.run x
@[inline] def PShareCommonM.run (x : PShareCommonM α) : α := PShareCommonT.run x

def shareCommon (a : α) : α :=
  (withShareCommon a : ShareCommonM α).run
