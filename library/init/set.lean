/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.logic init.collection

universe variables u v

def set (A : Type u) := A → Prop

def set_of {A : Type u} (p : A → Prop) : set A :=
p

namespace set
variables {A : Type u} {B : Type v}

def mem (a : A) (s : set A) :=
s a

infix ∈ := mem
notation a ∉ s := ¬ mem a s

def subset (s₁ s₂ : set A) : Prop :=
∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂
infix ⊆ := subset

def superset (s₁ s₂ : set A) : Prop :=
s₂ ⊆ s₁
infix ⊇ := superset

private def sep (p : A → Prop) (s : set A) : set A :=
{a | a ∈ s ∧ p a}

instance : separable A set :=
⟨sep⟩

private def empty : set A :=
λ a, false

private def insert (a : A) (s : set A) : set A :=
{b | b = a ∨ b ∈ s}

instance : insertable A set :=
⟨empty, insert⟩

def union (s₁ s₂ : set A) : set A :=
{a | a ∈ s₁ ∨ a ∈ s₂}
notation s₁ ∪ s₂ := union s₁ s₂

def inter (s₁ s₂ : set A) : set A :=
{a | a ∈ s₁ ∧ a ∈ s₂}
notation s₁ ∩ s₂ := inter s₁ s₂

def compl (s : set A) : set A :=
{a | a ∉ s}

instance : has_neg (set A) :=
⟨compl⟩

def diff (s t : set A) : set A :=
{a ∈ s | a ∉ t}
infix `\`:70 := diff

def powerset (s : set A) : set (set A) :=
{t | t ⊆ s}
prefix `𝒫`:100 := powerset

def image (f : A → B) (s : set A) : set B :=
{b | ∃ a, a ∈ s ∧ f a = b}
infix ` ' ` := image
end set
