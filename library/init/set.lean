/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.logic init.functor

universe variables u v

def set (A : Type u) := A → Prop

def set_of {A : Type u} (p : A → Prop) : set A :=
p

namespace set
variables {A : Type u} {B : Type v}

protected def mem (a : A) (s : set A) :=
s a

instance : has_mem A set :=
⟨set.mem⟩

protected def subset (s₁ s₂ : set A) :=
∀ a, a ∈ s₁ → a ∈ s₂

instance : has_subset (set A) :=
⟨set.subset⟩

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

protected def union (s₁ s₂ : set A) : set A :=
{a | a ∈ s₁ ∨ a ∈ s₂}

instance : has_union (set A) :=
⟨set.union⟩

protected def inter (s₁ s₂ : set A) : set A :=
{a | a ∈ s₁ ∧ a ∈ s₂}

instance : has_inter (set A) :=
⟨set.inter⟩

def compl (s : set A) : set A :=
{a | a ∉ s}

instance : has_neg (set A) :=
⟨compl⟩

protected def diff (s t : set A) : set A :=
{a ∈ s | a ∉ t}

instance : has_sdiff (set A) :=
⟨set.diff⟩

def powerset (s : set A) : set (set A) :=
{t | t ⊆ s}
prefix `𝒫`:100 := powerset

def image (f : A → B) (s : set A) : set B :=
{b | ∃ a, a ∈ s ∧ f a = b}

instance : functor set :=
⟨@set.image⟩

end set
