/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
module

prelude
public import Init.Data.UInt.Basic
public import Init.Control.State


namespace ShareCommon
/-
  The max sharing primitives are implemented internally.
  They use maps and sets of Lean objects. We have two versions:
  one using `HashMap` and `HashSet`, and another using
  `PersistentHashMap` and `PersistentHashSet`.
  These maps and sets are "instantiated here using the "unsafe"
  primitives `Object.eq`, `Object.hash`, and `ptrAddrUnsafe`. -/
abbrev Internal.Object : Type := NonScalar

unsafe def Internal.Object.ptrEq (a b : Object) : Bool :=
  ptrAddrUnsafe a == ptrAddrUnsafe b

unsafe abbrev Internal.Object.ptrHash (a : Object) : UInt64 :=
  ptrAddrUnsafe a |>.toUInt64

structure Internal.StateFactoryImpl where
  (Map Set : Type)
  mkState : Unit → Map × Set
  mapFind? (m : Map) (k : Internal.Object) : Option Internal.Object
  mapInsert (m : Map) (k v : Internal.Object) : Map
  setFind? (m : Set) (k : Internal.Object) : Option Internal.Object
  setInsert (m : Set) (o : Internal.Object) : Set

public opaque Internal.StateFactoryPointed : NonemptyType
public abbrev StateFactory : Type := Internal.StateFactoryPointed.type
instance : Nonempty StateFactory := Internal.StateFactoryPointed.property

@[extern "lean_sharecommon_eq"]
unsafe opaque Internal.Object.eq (a b : @& Internal.Object) : Bool

@[extern "lean_sharecommon_hash"]
unsafe opaque Internal.Object.hash (a : @& Internal.Object) : UInt64

public structure StateFactoryBuilder where
  Map (α _β : Type) [BEq α] [Hashable α] : Type
  mkMap {α β : Type} [BEq α] [Hashable α] (capacity : Nat) : Map α β
  mapFind? {α β : Type} [BEq α] [Hashable α] : Map α β → α → Option β
  mapInsert {α β : Type} [BEq α] [Hashable α] : Map α β → α → β → Map α β
  Set (α : Type) [BEq α] [Hashable α] : Type
  mkSet {α : Type} [BEq α] [Hashable α] (capacity : Nat) : Set α
  setFind? {α : Type} [BEq α] [Hashable α] : Set α → α → Option α
  setInsert {α : Type} [BEq α] [Hashable α] : Set α → α → Set α

unsafe def Internal.StateFactory.mkImpl : StateFactoryBuilder → StateFactory
  | { Map, mkMap, mapFind?, mapInsert, Set, mkSet, setFind?, setInsert } =>
    unsafeCast {
      Map := @Map Internal.Object Internal.Object ⟨Internal.Object.ptrEq⟩ ⟨Internal.Object.ptrHash⟩
      Set := @Set Internal.Object ⟨Internal.Object.eq⟩ ⟨Internal.Object.hash⟩
      mkState := fun _ => (
        @mkMap Internal.Object Internal.Object ⟨Internal.Object.ptrEq⟩ ⟨Internal.Object.ptrHash⟩ 1024,
        @mkSet Internal.Object ⟨Internal.Object.eq⟩ ⟨Internal.Object.hash⟩ 1024)
      mapFind? := @mapFind? Internal.Object Internal.Object ⟨Internal.Object.ptrEq⟩ ⟨Internal.Object.ptrHash⟩
      mapInsert := @mapInsert Internal.Object Internal.Object ⟨Internal.Object.ptrEq⟩ ⟨Internal.Object.ptrHash⟩
      setFind? := @setFind? Internal.Object ⟨Internal.Object.eq⟩ ⟨Internal.Object.hash⟩
      setInsert := @setInsert Internal.Object ⟨Internal.Object.eq⟩ ⟨Internal.Object.hash⟩
    : Internal.StateFactoryImpl }

@[implemented_by Internal.StateFactory.mkImpl]
public opaque StateFactory.mk : StateFactoryBuilder → StateFactory

unsafe def StateFactory.Internal.get : StateFactory → Internal.StateFactoryImpl := unsafeCast

/-- Internally `State` is implemented as a pair `ObjectMap` and `ObjectSet` -/
public opaque Internal.StatePointed (σ : StateFactory) : NonemptyType
public abbrev State (σ : StateFactory) : Type u := (Internal.StatePointed σ).type
public instance : Nonempty (State σ) := (Internal.StatePointed σ).property

unsafe def Internal.mkStateImpl (σ : StateFactory) : State σ := unsafeCast ((StateFactory.Internal.get σ).mkState ())
@[implemented_by Internal.mkStateImpl] public opaque State.mk (σ : StateFactory) : State σ
public instance : Inhabited (State σ) := ⟨.mk σ⟩

@[extern "lean_state_sharecommon"]
public def State.shareCommon {σ : @& StateFactory} (s : State σ) (a : α) : α × State σ := (a, s)

end ShareCommon

public class MonadShareCommon (m : Type u → Type v) where
  withShareCommon {α : Type u} : α → m α

public abbrev withShareCommon := @MonadShareCommon.withShareCommon

@[deprecated withShareCommon +typeChanged (since := "2026-11-24")]
public abbrev shareCommonM [MonadShareCommon m] (a : α) : m α :=
  withShareCommon a

public abbrev ShareCommonT (σ) (m : Type u → Type v) := StateT (ShareCommon.State σ) m
public abbrev ShareCommonM (σ) := ShareCommonT σ Id

@[specialize] public def ShareCommonT.withShareCommon [Monad m] (a : α) : ShareCommonT σ m α :=
  modifyGet fun s => s.shareCommon a

public instance ShareCommonT.monadShareCommon [Monad m] : MonadShareCommon (ShareCommonT σ m) where
  withShareCommon := ShareCommonT.withShareCommon

@[inline] public def ShareCommonT.run [Monad m] (x : ShareCommonT σ m α) : m α := x.run' default
@[inline] public def ShareCommonM.run (x : ShareCommonM σ α) : α := ShareCommonT.run x

/--
Returns a copy of `a` in which structurally equal subobjects are represented by the same object.

Only arrays, scalar arrays, strings, big numbers, and constructor objects are shared; closures,
thunks, tasks, references, and external objects are kept as they are. Sharing is local to one call:
results of separate calls do not share subobjects with each other.
-/
@[extern "lean_sharecommon_quick"]
public def ShareCommon.shareCommon (a : @& α) : α := a

@[deprecated ShareCommon.shareCommon (since := "2026-11-24")]
public abbrev ShareCommon.shareCommon' := @ShareCommon.shareCommon
