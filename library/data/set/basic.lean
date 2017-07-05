/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad, Leonardo de Moura
-/
namespace set
universes u
variable {α : Type u}

lemma ext {a b : set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
funext (assume x, propext (h x))

lemma subset.refl (a : set α) : a ⊆ a := assume x, assume H, H

lemma subset.trans {a b c : set α} (subab : a ⊆ b) (subbc : b ⊆ c) : a ⊆ c :=
assume x, assume ax, subbc (subab ax)

lemma subset.antisymm {a b : set α} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b :=
ext (λ x, iff.intro (λ ina, h₁ ina) (λ inb, h₂ inb))

-- an alterantive name
lemma eq_of_subset_of_subset {a b : set α} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b :=
subset.antisymm h₁ h₂

lemma mem_of_subset_of_mem {s₁ s₂ : set α} {a : α} : s₁ ⊆ s₂ → a ∈ s₁ → a ∈ s₂ :=
assume h₁ h₂, h₁ h₂

lemma not_mem_empty (x : α) : ¬ (x ∈ (∅ : set α)) :=
assume h : x ∈ ∅, h

lemma mem_empty_eq (x : α) : x ∈ (∅ : set α) = false :=
rfl

lemma eq_empty_of_forall_not_mem {s : set α} (h : ∀ x, x ∉ s) : s = ∅ :=
ext (assume x, iff.intro
  (assume xs, absurd xs (h x))
  (assume xe, absurd xe (not_mem_empty _)))

lemma ne_empty_of_mem {s : set α} {x : α} (h : x ∈ s) : s ≠ ∅ :=
  begin intro hs, rewrite hs at h, apply not_mem_empty _ h end

lemma empty_subset (s : set α) : ∅ ⊆ s :=
assume x, assume h, false.elim h

lemma eq_empty_of_subset_empty {s : set α} (h : s ⊆ ∅) : s = ∅ :=
subset.antisymm h (empty_subset s)

lemma union_comm (a b : set α) : a ∪ b = b ∪ a :=
ext (assume x, or.comm)

lemma union_assoc (a b c : set α) : (a ∪ b) ∪ c = a ∪ (b ∪ c) :=
ext (assume x, or.assoc)

instance union_is_assoc : is_associative (set α) (∪) :=
⟨union_assoc⟩

instance union_is_comm : is_commutative (set α) (∪) :=
⟨union_comm⟩

lemma union_self (a : set α) : a ∪ a = a :=
ext (assume x, or_self _)

lemma union_empty (a : set α) : a ∪ ∅ = a :=
ext (assume x, or_false _)

lemma empty_union (a : set α) : ∅ ∪ a = a :=
ext (assume x, false_or _)

lemma inter_comm (a b : set α) : a ∩ b = b ∩ a :=
ext (assume x, and.comm)

lemma inter_assoc (a b c : set α) : (a ∩ b) ∩ c = a ∩ (b ∩ c) :=
ext (assume x, and.assoc)

instance inter_is_assoc : is_associative (set α) (∩) :=
⟨inter_assoc⟩

instance inter_is_comm : is_commutative (set α) (∩) :=
⟨inter_comm⟩

lemma inter_self (a : set α) : a ∩ a = a :=
ext (assume x, and_self _)

lemma inter_empty (a : set α) : a ∩ ∅ = ∅ :=
ext (assume x, and_false _)

lemma empty_inter (a : set α) : ∅ ∩ a = ∅ :=
ext (assume x, false_and _)

end set
