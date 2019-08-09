/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.rbmap.basic
universes u v w

def RBTree (α : Type u) (lt : α → α → Bool) : Type u :=
RBMap α Unit lt

@[inline] def mkRBTree (α : Type u) (lt : α → α → Bool) : RBTree α lt :=
mkRBMap α Unit lt

instance (α : Type u) (lt : α → α → Bool) : HasEmptyc (RBTree α lt) :=
⟨mkRBTree α lt⟩

namespace RBTree
variables {α : Type u} {β : Type v} {lt : α → α → Bool}

@[inline] def empty : RBTree α lt :=
RBMap.empty

@[inline] def depth (f : Nat → Nat → Nat) (t : RBTree α lt) : Nat :=
RBMap.depth f t

@[inline] def fold (f : β → α → β) (b : β) (t : RBTree α lt) : β :=
RBMap.fold (fun r a _ => f r a) b t

@[inline] def revFold (f : β → α → β) (b : β) (t : RBTree α lt) : β :=
RBMap.revFold (fun r a _ => f r a) b t

@[inline] def mfold {m : Type v → Type w} [Monad m] (f : β → α → m β) (b : β) (t : RBTree α lt) : m β :=
RBMap.mfold (fun r a _ => f r a) b t

@[inline] def mfor {m : Type v → Type w} [Monad m] (f : α → m β) (t : RBTree α lt) : m PUnit :=
t.mfold (fun _ a => f a *> pure ⟨⟩) ⟨⟩

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

instance [HasRepr α] : HasRepr (RBTree α lt) :=
⟨fun t => "rbtreeOf " ++ repr t.toList⟩

@[inline] def insert (t : RBTree α lt) (a : α) : RBTree α lt :=
RBMap.insert t a ()

@[inline] def erase (t : RBTree α lt) (a : α) : RBTree α lt :=
RBMap.erase t a

@[specialize] def ofList : List α → RBTree α lt
| []    => mkRBTree _ _
| x::xs => (ofList xs).insert x

@[inline] def find (t : RBTree α lt) (a : α) : Option α :=
match RBMap.findCore t a with
| some ⟨a, _⟩ => some a
| none        => none

@[inline] def contains (t : RBTree α lt) (a : α) : Bool :=
(t.find a).isSome

def fromList (l : List α) (lt : α → α → Bool) : RBTree α lt :=
l.foldl insert (mkRBTree α lt)

@[inline] def all (t : RBTree α lt) (p : α → Bool) : Bool :=
RBMap.all t (fun a _ => p a)

@[inline] def any (t : RBTree α lt) (p : α → Bool) : Bool :=
RBMap.any t (fun a _ => p a)

def subset (t₁ t₂ : RBTree α lt) : Bool :=
t₁.all $ fun a => (t₂.find a).toBool

def seteq (t₁ t₂ : RBTree α lt) : Bool :=
subset t₁ t₂ && subset t₂ t₁

end RBTree

def rbtreeOf {α : Type u} (l : List α) (lt : α → α → Bool) : RBTree α lt :=
RBTree.fromList l lt
