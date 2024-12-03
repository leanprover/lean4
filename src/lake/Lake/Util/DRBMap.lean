/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mac Malone
-/
prelude
import Lean.Data.RBMap
import Lake.Util.Compare

namespace Lake
open Lean RBNode

/-!
This module includes a dependently typed adaption of the `Lean.RBMap`
defined in `Lean.Data.RBMap` module of the Lean core. Most of the code is
copied directly from there with only minor edits.
-/

instance inhabitedOfEmptyCollection [EmptyCollection α] : Inhabited α where
  default := {}

@[specialize] def RBNode.dFind {α : Type u} {β : α → Type v}
(cmp : α → α → Ordering) [h : EqOfCmpWrt α β cmp] : RBNode α β → (k : α) → Option (β k)
  | leaf,             _ => none
  | node _ a ky vy b, x =>
    match ho:cmp x ky with
    | Ordering.lt => dFind cmp a x
    | Ordering.gt => dFind cmp b x
    | Ordering.eq => some <| cast (by rw [eq_of_cmp_wrt (f := β) ho]) vy

/-- A Dependently typed `RBMap`. -/
def DRBMap (α : Type u) (β : α → Type v) (cmp : α → α → Ordering) : Type (max u v) :=
  {t : RBNode α β // t.WellFormed cmp }

instance : Coe (DRBMap α (fun _ => β) cmp) (RBMap α β cmp) := ⟨id⟩

@[inline] def mkDRBMap (α : Type u) (β : α → Type v) (cmp : α → α → Ordering) : DRBMap α β cmp :=
  ⟨leaf, WellFormed.leafWff⟩

@[inline] def DRBMap.empty {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} : DRBMap α β cmp :=
  mkDRBMap ..

instance (α : Type u) (β : α → Type v) (cmp : α → α → Ordering) : EmptyCollection (DRBMap α β cmp) :=
  ⟨DRBMap.empty⟩

namespace DRBMap
variable {α : Type u} {β : α → Type v} {σ : Type w} {cmp : α → α → Ordering}

def depth (f : Nat → Nat → Nat) (t : DRBMap α β cmp) : Nat :=
  t.val.depth f

@[inline] def fold (f : σ → (k : α) → β k → σ) : (init : σ) → DRBMap α β cmp → σ
  | b, ⟨t, _⟩ => t.fold f b

@[inline] def revFold (f : σ → (k : α) → β k → σ) : (init : σ) → DRBMap α β cmp → σ
  | b, ⟨t, _⟩ => t.revFold f b

@[inline] def foldM [Monad m] (f : σ → (k : α) → β k → m σ) : (init : σ) → DRBMap α β cmp → m σ
  | b, ⟨t, _⟩ => t.foldM f b

@[inline] def forM [Monad m] (f : (k : α) → β k → m PUnit) (t : DRBMap α β cmp) : m PUnit :=
  t.foldM (fun _ k v => f k v) ⟨⟩

@[inline] protected def forIn [Monad m] (t : DRBMap α β cmp) (init : σ) (f : ((k : α) × β k) → σ → m (ForInStep σ)) : m σ :=
  t.val.forIn init (fun a b acc => f ⟨a, b⟩ acc)

instance : ForIn m (DRBMap α β cmp) ((k : α) × β k) where
  forIn := DRBMap.forIn

@[inline] def isEmpty : DRBMap α β cmp → Bool
  | ⟨leaf, _⟩ => true
  | _         => false

@[specialize] def toList : DRBMap α β cmp → List ((k : α) × β k)
  | ⟨t, _⟩ => t.revFold (fun ps k v => ⟨k, v⟩::ps) []

@[inline] protected def min : DRBMap α β cmp → Option ((k : α) × β k)
  | ⟨t, _⟩ =>
    match t.min with
    | some ⟨k, v⟩ => some ⟨k, v⟩
    | none        => none

@[inline] protected def max : DRBMap α β cmp → Option ((k : α) × β k)
  | ⟨t, _⟩ =>
    match t.max with
    | some ⟨k, v⟩ => some ⟨k, v⟩
    | none        => none

instance [Repr ((k : α) × β k)] : Repr (DRBMap α β cmp) where
  reprPrec m prec := Repr.addAppParen ("Lake.drbmapOf " ++ repr m.toList) prec

@[inline] def insert : DRBMap α β cmp → (k : α) → β k → DRBMap α β cmp
  | ⟨t, w⟩, k, v => ⟨t.insert cmp k v, WellFormed.insertWff w rfl⟩

@[inline] def erase : DRBMap α β cmp → α → DRBMap α β cmp
  | ⟨t, w⟩, k => ⟨t.erase cmp k, WellFormed.eraseWff w rfl⟩

@[specialize] def ofList : List ((k : α) × β k) → DRBMap α β cmp
  | []        => mkDRBMap ..
  | ⟨k,v⟩::xs => (ofList xs).insert k v

@[inline] def findCore? : DRBMap α β cmp → α → Option ((k : α) × β k)
  | ⟨t, _⟩, x => t.findCore cmp x

@[inline] def find? [EqOfCmpWrt α β cmp] : DRBMap α β cmp → (k : α) → Option (β k)
  | ⟨t, _⟩, x => RBNode.dFind cmp t x

@[inline] def findD [EqOfCmpWrt α β cmp] (t : DRBMap α β cmp) (k : α) (v₀ : β k) : β k :=
  (t.find? k).getD v₀

/-- (lowerBound k) retrieves the kv pair of the largest key smaller than or equal to `k`,
    if it exists. -/
@[inline] def lowerBound : DRBMap α β cmp → α → Option ((k : α) × β k)
  | ⟨t, _⟩, x => t.lowerBound cmp x none

@[inline] def contains [EqOfCmpWrt α β cmp] (t : DRBMap α β cmp) (k : α) : Bool :=
  (t.find? k).isSome

@[inline] def fromList (l : List ((k : α) × β k)) (cmp : α → α → Ordering) : DRBMap α β cmp :=
  l.foldl (fun r p => r.insert p.1 p.2) (mkDRBMap α β cmp)

@[inline] def all : DRBMap α β cmp → ((k : α) → β k → Bool) → Bool
  | ⟨t, _⟩, p => t.all p

@[inline] def any : DRBMap α β cmp → ((k : α) → β k → Bool) → Bool
  | ⟨t, _⟩, p => t.any p

def size (m : DRBMap α β cmp) : Nat :=
  m.fold (fun sz _ _ => sz+1) 0

def maxDepth (t : DRBMap α β cmp) : Nat :=
  t.val.depth Nat.max

@[inline] def min! [Inhabited ((k : α) × β k)] (t : DRBMap α β cmp) : (k : α) × β k :=
  match t.min with
  | some p => p
  | none   => panic! "map is empty"

@[inline] def max! [Inhabited ((k : α) × β k)] (t : DRBMap α β cmp) : (k : α) × β k :=
  match t.max with
  | some p => p
  | none   => panic! "map is empty"

@[inline] def find! [EqOfCmpWrt α β cmp] (t : DRBMap α β cmp) (k : α) [Inhabited (β k)] : β k :=
  match t.find? k with
  | some b => b
  | none   => panic! "key is not in the map"

end DRBMap

def drbmapOf {α : Type u} {β : α → Type v} (l : List ((k : α) × (β k))) (cmp : α → α → Ordering) : DRBMap α β cmp :=
  DRBMap.fromList l cmp
