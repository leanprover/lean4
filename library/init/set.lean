/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.logic init.collection

universe variables u v

definition set (A : Type u) := A → Prop

definition set_of {A : Type u} (p : A → Prop) : set A :=
p

namespace set
variables {A : Type u} {B : Type v}

definition mem (a : A) (s : set A) :=
s a

infix ∈ := mem
notation a ∉ s := ¬ mem a s

definition subset (s₁ s₂ : set A) : Prop :=
∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂
infix ⊆ := subset

definition superset (s₁ s₂ : set A) : Prop :=
s₂ ⊆ s₁
infix ⊇ := superset

private definition sep (p : A → Prop) (s : set A) : set A :=
{a | a ∈ s ∧ p a}

instance : separable A set :=
⟨sep⟩

private definition empty : set A :=
λ a, false

private definition insert (a : A) (s : set A) : set A :=
{b | b = a ∨ b ∈ s}

instance : insertable A set :=
⟨empty, insert⟩

definition union (s₁ s₂ : set A) : set A :=
{a | a ∈ s₁ ∨ a ∈ s₂}
notation s₁ ∪ s₂ := union s₁ s₂

definition inter (s₁ s₂ : set A) : set A :=
{a | a ∈ s₁ ∧ a ∈ s₂}
notation s₁ ∩ s₂ := inter s₁ s₂

definition compl (s : set A) : set A :=
{a | a ∉ s}

instance : has_neg (set A) :=
⟨compl⟩

definition diff (s t : set A) : set A :=
{a ∈ s | a ∉ t}
infix `\`:70 := diff

definition powerset (s : set A) : set (set A) :=
{t | t ⊆ s}
prefix `𝒫`:100 := powerset

definition image (f : A → B) (s : set A) : set B :=
{b | ∃ a, a ∈ s ∧ f a = b}
infix ` ' ` := image
end set
