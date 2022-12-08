/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Data.RBMap
namespace Lean
universe u v w

def RBTree (α : Type u) (cmp : α → α → Ordering) : Type u :=
  RBMap α Unit cmp

instance : Inhabited (RBTree α p) where
  default := RBMap.empty

@[inline] def mkRBTree (α : Type u) (cmp : α → α → Ordering) : RBTree α cmp :=
  mkRBMap α Unit cmp

instance (α : Type u) (cmp : α → α → Ordering) : EmptyCollection (RBTree α cmp) :=
  ⟨mkRBTree α cmp⟩

namespace RBTree
variable {α : Type u} {β : Type v} {cmp : α → α → Ordering}

@[inline] def empty : RBTree α cmp :=
  RBMap.empty

@[inline] def depth (f : Nat → Nat → Nat) (t : RBTree α cmp) : Nat :=
  RBMap.depth f t

@[inline] def fold (f : β → α → β) (init : β) (t : RBTree α cmp) : β :=
  RBMap.fold (fun r a _ => f r a) init t

@[inline] def revFold (f : β → α → β) (init : β) (t : RBTree α cmp) : β :=
  RBMap.revFold (fun r a _ => f r a) init t

@[inline] def foldM {m : Type v → Type w} [Monad m] (f : β → α → m β) (init : β) (t : RBTree α cmp) : m β :=
  RBMap.foldM (fun r a _ => f r a) init t

@[inline] def forM {m : Type v → Type w} [Monad m] (f : α → m PUnit) (t : RBTree α cmp) : m PUnit :=
  t.foldM (fun _ a => f a) ⟨⟩

@[inline] protected def forIn [Monad m] (t : RBTree α cmp) (init : σ) (f : α → σ → m (ForInStep σ)) : m σ :=
  t.val.forIn init (fun a _ acc => f a acc)

instance : ForIn m (RBTree α cmp) α where
  forIn := RBTree.forIn

@[inline] def isEmpty (t : RBTree α cmp) : Bool :=
  RBMap.isEmpty t

@[specialize] def toList (t : RBTree α cmp) : List α :=
  t.revFold (fun as a => a::as) []

@[specialize] def toArray (t : RBTree α cmp) : Array α :=
  t.fold (fun as a => as.push a) #[]

@[inline] protected def min (t : RBTree α cmp) : Option α :=
  match RBMap.min t with
  | some ⟨a, _⟩ => some a
  | none        => none

@[inline] protected def max (t : RBTree α cmp) : Option α :=
  match RBMap.max t with
  | some ⟨a, _⟩ => some a
  | none        => none

instance [Repr α] : Repr (RBTree α cmp) where
  reprPrec t prec := Repr.addAppParen ("Lean.rbtreeOf " ++ repr t.toList) prec

@[inline] def insert (t : RBTree α cmp) (a : α) : RBTree α cmp :=
  RBMap.insert t a ()

@[inline] def erase (t : RBTree α cmp) (a : α) : RBTree α cmp :=
  RBMap.erase t a

@[specialize] def ofList : List α → RBTree α cmp
  | []    => mkRBTree ..
  | x::xs => (ofList xs).insert x

@[inline] def find? (t : RBTree α cmp) (a : α) : Option α :=
  match RBMap.findCore? t a with
  | some ⟨a, _⟩ => some a
  | none        => none

@[inline] def contains (t : RBTree α cmp) (a : α) : Bool :=
  (t.find? a).isSome

def fromList (l : List α) (cmp : α → α → Ordering) : RBTree α cmp :=
  l.foldl insert (mkRBTree α cmp)

def fromArray (l : Array α) (cmp : α → α → Ordering) : RBTree α cmp :=
  l.foldl insert (mkRBTree α cmp)

@[inline] def all (t : RBTree α cmp) (p : α → Bool) : Bool :=
  RBMap.all t (fun a _ => p a)

@[inline] def any (t : RBTree α cmp) (p : α → Bool) : Bool :=
  RBMap.any t (fun a _ => p a)

def subset (t₁ t₂ : RBTree α cmp) : Bool :=
  t₁.all fun a => (t₂.find? a).toBool

def seteq (t₁ t₂ : RBTree α cmp) : Bool :=
  subset t₁ t₂ && subset t₂ t₁

def union (t₁ t₂ : RBTree α cmp) : RBTree α cmp :=
  if t₁.isEmpty then
    t₂
  else
    t₂.fold .insert t₁

def diff (t₁ t₂ : RBTree α cmp) : RBTree α cmp :=
  t₂.fold .erase t₁

end RBTree

def rbtreeOf {α : Type u} (l : List α) (cmp : α → α → Ordering) : RBTree α cmp :=
  RBTree.fromList l cmp
