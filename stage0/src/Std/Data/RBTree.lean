/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Std.Data.RBMap
namespace Std
universes u v w

def RBTree (α : Type u) (lt : α → α → Bool) : Type u :=
  RBMap α Unit lt

instance : Inhabited (RBTree α p) where
  default := RBMap.empty

@[inline] def mkRBTree (α : Type u) (lt : α → α → Bool) : RBTree α lt :=
  mkRBMap α Unit lt

instance (α : Type u) (lt : α → α → Bool) : EmptyCollection (RBTree α lt) :=
  ⟨mkRBTree α lt⟩

namespace RBTree
variables {α : Type u} {β : Type v} {lt : α → α → Bool}

@[inline] def empty : RBTree α lt :=
  RBMap.empty

@[inline] def depth (f : Nat → Nat → Nat) (t : RBTree α lt) : Nat :=
  RBMap.depth f t

@[inline] def fold (f : β → α → β) (init : β) (t : RBTree α lt) : β :=
  RBMap.fold (fun r a _ => f r a) init t

@[inline] def revFold (f : β → α → β) (init : β) (t : RBTree α lt) : β :=
  RBMap.revFold (fun r a _ => f r a) init t

@[inline] def foldM {m : Type v → Type w} [Monad m] (f : β → α → m β) (init : β) (t : RBTree α lt) : m β :=
  RBMap.foldM (fun r a _ => f r a) init t

@[inline] def forM {m : Type v → Type w} [Monad m] (f : α → m PUnit) (t : RBTree α lt) : m PUnit :=
  t.foldM (fun _ a => f a) ⟨⟩

@[inline] def forIn [Monad m] (t : RBTree α lt) (init : σ) (f : α → σ → m (ForInStep σ)) : m σ :=
  t.val.forIn init (fun a _ acc => f a acc)

@[inline] def isEmpty (t : RBTree α lt) : Bool :=
  RBMap.isEmpty t

@[specialize] def toList (t : RBTree α lt) : List α :=
  t.revFold (fun as a => a::as) []

@[inline] protected def min (t : RBTree α lt) : Option α :=
  match RBMap.min t with
  | some ⟨a, _⟩ => some a
  | none        => none

@[inline] protected def max (t : RBTree α lt) : Option α :=
  match RBMap.max t with
  | some ⟨a, _⟩ => some a
  | none        => none

instance [Repr α] : Repr (RBTree α lt) where
  reprPrec t prec := Repr.addAppParen ("Std.rbtreeOf " ++ repr t.toList) prec

@[inline] def insert (t : RBTree α lt) (a : α) : RBTree α lt :=
  RBMap.insert t a ()

@[inline] def erase (t : RBTree α lt) (a : α) : RBTree α lt :=
  RBMap.erase t a

@[specialize] def ofList : List α → RBTree α lt
  | []    => mkRBTree ..
  | x::xs => (ofList xs).insert x

@[inline] def find? (t : RBTree α lt) (a : α) : Option α :=
  match RBMap.findCore? t a with
  | some ⟨a, _⟩ => some a
  | none        => none

@[inline] def contains (t : RBTree α lt) (a : α) : Bool :=
  (t.find? a).isSome

def fromList (l : List α) (lt : α → α → Bool) : RBTree α lt :=
  l.foldl insert (mkRBTree α lt)

@[inline] def all (t : RBTree α lt) (p : α → Bool) : Bool :=
  RBMap.all t (fun a _ => p a)

@[inline] def any (t : RBTree α lt) (p : α → Bool) : Bool :=
  RBMap.any t (fun a _ => p a)

def subset (t₁ t₂ : RBTree α lt) : Bool :=
  t₁.all fun a => (t₂.find? a).toBool

def seteq (t₁ t₂ : RBTree α lt) : Bool :=
  subset t₁ t₂ && subset t₂ t₁

end RBTree

def rbtreeOf {α : Type u} (l : List α) (lt : α → α → Bool) : RBTree α lt :=
  RBTree.fromList l lt
end Std
