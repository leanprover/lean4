/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Util
import Init.Data.HashMap
import Init.Data.HashSet
import Init.Data.PersistentHashSet
import Init.Data.PersistentHashMap
import Init.Control.State

universes u v

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

unsafe def Object.ptrHash (a : Object) : USize :=
ptrAddrUnsafe a

@[extern "lean_sharecommon_eq"]
unsafe constant Object.eq (a b : @& Object) : Bool := arbitrary _

@[extern "lean_sharecommon_hash"]
unsafe constant Object.hash (a : @& Object) : USize := arbitrary _

unsafe def ObjectMap : Type := @HashMap Object Object ⟨Object.ptrEq⟩ ⟨Object.ptrHash⟩
unsafe def ObjectSet : Type := @HashSet Object ⟨Object.eq⟩ ⟨Object.hash⟩
unsafe def ObjectPersistentMap : Type := @PersistentHashMap Object Object ⟨Object.ptrEq⟩ ⟨Object.ptrHash⟩
unsafe def ObjectPersistentSet : Type := @PersistentHashSet Object ⟨Object.eq⟩ ⟨Object.hash⟩

@[export lean_mk_object_map]
unsafe def mkObjectMap : Unit → ObjectMap :=
fun _ => @mkHashMap Object Object ⟨Object.ptrEq⟩ ⟨Object.ptrHash⟩ 1024

@[export lean_object_map_find]
unsafe def ObjectMap.find? (m : ObjectMap) (k : Object) : Option Object :=
@HashMap.find? Object Object ⟨Object.ptrEq⟩ ⟨Object.ptrHash⟩ m k

@[export lean_object_map_insert]
unsafe def ObjectMap.insert (m : ObjectMap) (k v : Object) : ObjectMap :=
@HashMap.insert Object Object ⟨Object.ptrEq⟩ ⟨Object.ptrHash⟩ m k v

@[export lean_mk_object_set]
unsafe def mkObjectSet : Unit → ObjectSet :=
fun _ => @mkHashSet Object ⟨Object.eq⟩ ⟨Object.hash⟩ 1024

@[export lean_object_set_find]
unsafe def ObjectSet.find? (s : ObjectSet) (o : Object) : Option Object :=
@HashSet.find? Object ⟨Object.eq⟩ ⟨Object.hash⟩ s o

@[export lean_object_set_insert]
unsafe def ObjectSet.insert (s : ObjectSet) (o : Object) : ObjectSet :=
@HashSet.insert Object ⟨Object.eq⟩ ⟨Object.hash⟩ s o

@[export lean_mk_object_pmap]
unsafe def mkObjectPersistentMap : Unit → ObjectPersistentMap :=
fun _ => @PersistentHashMap.empty Object Object ⟨Object.ptrEq⟩ ⟨Object.ptrHash⟩

@[export lean_object_pmap_find]
unsafe def ObjectPersistentMap.find? (m : ObjectPersistentMap) (k : Object) : Option Object :=
@PersistentHashMap.find? Object Object ⟨Object.ptrEq⟩ ⟨Object.ptrHash⟩ m k

@[export lean_object_pmap_insert]
unsafe def ObjectPersistentMap.insert (m : ObjectPersistentMap) (k v : Object) : ObjectPersistentMap :=
@PersistentHashMap.insert Object Object ⟨Object.ptrEq⟩ ⟨Object.ptrHash⟩ m k v

@[export lean_mk_object_pset]
unsafe def mkObjectPersistentSet : Unit → ObjectPersistentSet :=
fun _ => @PersistentHashSet.empty Object ⟨Object.eq⟩ ⟨Object.hash⟩

@[export lean_object_pset_find]
unsafe def ObjectPersistentSet.find? (s : ObjectPersistentSet) (o : Object) : Option Object :=
@PersistentHashSet.find? Object ⟨Object.eq⟩ ⟨Object.hash⟩ s o

@[export lean_object_pset_insert]
unsafe def ObjectPersistentSet.insert (s : ObjectPersistentSet) (o : Object) : ObjectPersistentSet :=
@PersistentHashSet.insert Object ⟨Object.eq⟩ ⟨Object.hash⟩ s o

/- Internally `State` is implemented as a pair `ObjectMap` and `ObjectSet` -/
constant StatePointed : PointedType := arbitrary _
abbrev State : Type u := StatePointed.type
@[extern "lean_sharecommon_mk_state"]
constant mkState : Unit → State := fun _ => StatePointed.val
def State.empty : State := mkState ()
instance State.inhabited : Inhabited State := ⟨State.empty⟩

/- Internally `PersistentState` is implemented as a pair `ObjectPersistentMap` and `ObjectPersistentSet` -/
constant PersistentStatePointed : PointedType := arbitrary _
abbrev PersistentState : Type u := PersistentStatePointed.type
@[extern "lean_sharecommon_mk_pstate"]
constant mkPersistentState : Unit → PersistentState := fun _ => PersistentStatePointed.val
def PersistentState.empty : PersistentState := mkPersistentState ()
instance PersistentState.inhabited : Inhabited PersistentState := ⟨PersistentState.empty⟩
abbrev PState : Type u := PersistentState

@[extern "lean_state_sharecommon"]
def State.shareCommon {α} (s : State) (a : α) : α × State :=
(a, s)

@[extern "lean_persistent_state_sharecommon"]
def PersistentState.shareCommon {α} (s : PersistentState) (a : α) : α × PersistentState :=
(a, s)

end ShareCommon

class MonadShareCommon (m : Type u → Type v) :=
(withShareCommon {} {α : Type u} : α → m α)

export MonadShareCommon (withShareCommon)

abbrev shareCommonM {α : Type u} {m : Type u → Type v} [MonadShareCommon m] (a : α) : m α :=
withShareCommon a

abbrev ShareCommonT (m : Type u → Type v)  := StateT ShareCommon.State m
abbrev PShareCommonT (m : Type u → Type v) := StateT ShareCommon.PState m
abbrev ShareCommonM := ShareCommonT Id
abbrev PShareCommonM := PShareCommonT Id

@[specialize] def ShareCommonT.withShareCommon {m : Type u → Type v} [Monad m] {α : Type u} (a : α) : ShareCommonT m α :=
modifyGet $ fun s => s.shareCommon a

@[specialize] def PShareCommonT.withShareCommon {m : Type u → Type v} [Monad m] {α : Type u} (a : α) : PShareCommonT m α :=
modifyGet $ fun s => s.shareCommon a

instance ShareCommonT.monadShareCommon {m : Type u → Type v} [Monad m] : MonadShareCommon (ShareCommonT m) :=
{ withShareCommon := @ShareCommonT.withShareCommon _ _ }

instance PShareCommonT.monadShareCommon {m : Type u → Type v} [Monad m] : MonadShareCommon (PShareCommonT m) :=
{ withShareCommon := @PShareCommonT.withShareCommon _ _ }

@[inline] def ShareCommonT.run {m : Type u → Type v} [Monad m] {α : Type u} (x : ShareCommonT m α) : m α :=
x.run' ShareCommon.State.empty

@[inline] def PShareCommonT.run {m : Type u → Type v} [Monad m] {α : Type u} (x : PShareCommonT m α) : m α :=
x.run' ShareCommon.PersistentState.empty

def shareCommon {α} (a : α) : α :=
(withShareCommon a : ShareCommonM α).run
