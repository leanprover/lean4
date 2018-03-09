/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.interactive
import init.category.lawful

universes u v
def set (α : Type u) := α → Prop

def set_of {α : Type u} (p : α → Prop) : set α :=
p

namespace set
variables {α : Type u} {β : Type v}

protected def mem (a : α) (s : set α) :=
s a

instance : has_mem α (set α) :=
⟨set.mem⟩

protected def subset (s₁ s₂ : set α) :=
∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂

instance : has_subset (set α) :=
⟨set.subset⟩

protected def sep (p : α → Prop) (s : set α) : set α :=
{a | a ∈ s ∧ p a}

instance : has_sep α (set α) :=
⟨set.sep⟩

instance : has_emptyc (set α) :=
⟨λ a, false⟩

def univ : set α :=
λ a, true

protected def insert (a : α) (s : set α) : set α :=
{b | b = a ∨ b ∈ s}

instance : has_insert α (set α) :=
⟨set.insert⟩

protected def union (s₁ s₂ : set α) : set α :=
{a | a ∈ s₁ ∨ a ∈ s₂}

instance : has_union (set α) :=
⟨set.union⟩

protected def inter (s₁ s₂ : set α) : set α :=
{a | a ∈ s₁ ∧ a ∈ s₂}

instance : has_inter (set α) :=
⟨set.inter⟩

def compl (s : set α) : set α :=
{a | a ∉ s}

instance : has_neg (set α) :=
⟨compl⟩

protected def diff (s t : set α) : set α :=
{a ∈ s | a ∉ t}

instance : has_sdiff (set α) :=
⟨set.diff⟩

def powerset (s : set α) : set (set α) :=
{t | t ⊆ s}
prefix `𝒫`:100 := powerset

@[reducible]
def sUnion (s : set (set α)) : set α := {t | ∃ a ∈ s, t ∈ a}
prefix `⋃₀`:110 := sUnion

def image (f : α → β) (s : set α) : set β :=
{b | ∃ a, a ∈ s ∧ f a = b}

instance : functor set :=
{ map := @set.image }

instance : is_lawful_functor set :=
{ id_map := begin
    intros _ s, funext b,
    dsimp [image, set_of],
    exact propext ⟨λ ⟨b', ⟨_, _⟩⟩, ‹b' = b› ▸ ‹s b'›,
                   λ _, ⟨b, ⟨‹s b›, rfl⟩⟩⟩,
  end,
  comp_map := begin
    intros, funext c,
    dsimp [image, set_of, function.comp],
    exact propext ⟨λ ⟨a, ⟨h₁, h₂⟩⟩, ⟨g a, ⟨⟨a, ⟨h₁, rfl⟩⟩, h₂⟩⟩,
                   λ ⟨b, ⟨⟨a, ⟨h₁, h₂⟩⟩, h₃⟩⟩, ⟨a, ⟨h₁, h₂.symm ▸ h₃⟩⟩⟩
  end }

end set
