/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.rbmap.basic
universes u v w

def Rbtree (α : Type u) (lt : α → α → Prop) : Type u :=
Rbmap α Unit lt

@[inline] def mkRbtree (α : Type u) (lt : α → α → Prop) : Rbtree α lt :=
mkRbmap α Unit lt

namespace Rbtree
variables {α : Type u} {β : Type v} {lt : α → α → Prop}

@[inline] def depth (f : Nat → Nat → Nat) (t : Rbtree α lt) : Nat :=
Rbmap.depth f t

@[inline] def fold (f : α → β → β) (t : Rbtree α lt) (b : β) : β :=
Rbmap.fold (λ a _ r, f a r) t b

@[inline] def revFold (f : α → β → β) (t : Rbtree α lt) (b : β) : β :=
Rbmap.revFold (λ a _ r, f a r) t b

@[inline] def mfold {m : Type v → Type w} [Monad m] (f : α → β → m β) (t : Rbtree α lt) (b : β) : m β :=
Rbmap.mfold (λ a _ r, f a r) t b

@[inline] def mfor {m : Type v → Type w} [Monad m] (f : α → m β) (t : Rbtree α lt) : m Punit :=
t.mfold (λ a _, f a *> pure ⟨⟩) ⟨⟩

@[inline] def Empty (t : Rbtree α lt) : Bool :=
Rbmap.Empty t

@[specialize] def toList (t : Rbtree α lt) : List α :=
t.revFold (::) []

@[inline] protected def min (t : Rbtree α lt) : Option α :=
match Rbmap.min t with
| some ⟨a, _⟩ := some a
| none        := none

@[inline] protected def max (t : Rbtree α lt) : Option α :=
match Rbmap.max t with
| some ⟨a, _⟩ := some a
| none        := none

instance [HasRepr α] : HasRepr (Rbtree α lt) :=
⟨λ t, "rbtreeOf " ++ repr t.toList⟩

variables [decidableRel lt]

@[inline] def insert (t : Rbtree α lt) (a : α) : Rbtree α lt :=
Rbmap.insert t a ()

@[specialize] def ofList : List α → Rbtree α lt
| []      := mkRbtree _ _
| (x::xs) := (ofList xs).insert x

def find (t : Rbtree α lt) (a : α) : Option α :=
match Rbmap.findCore t a with
| some ⟨a, _⟩ := some a
| none        := none

@[inline] def contains (t : Rbtree α lt) (a : α) : Bool :=
(t.find a).isSome

def fromList (l : List α) (lt : α → α → Prop) [decidableRel lt] : Rbtree α lt :=
l.foldl insert (mkRbtree α lt)

@[inline] def all (t : Rbtree α lt) (p : α → Bool) : Bool :=
Rbmap.all t (λ a _, p a)

@[inline] def any (t : Rbtree α lt) (p : α → Bool) : Bool :=
Rbmap.any t (λ a _, p a)

def subset (t₁ t₂ : Rbtree α lt) : Bool :=
t₁.all $ λ a, (t₂.find a).toBool

def seteq (t₁ t₂ : Rbtree α lt) : Bool :=
subset t₁ t₂ && subset t₂ t₁

end Rbtree

def rbtreeOf {α : Type u} (l : List α) (lt : α → α → Prop) [decidableRel lt] : Rbtree α lt :=
Rbtree.fromList l lt
