/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.ordering.basic init.meta init.algebra.classes init.ite_simp
set_option default_priority 100

universes u

namespace ordering
/- Delete the following simp lemmas as soon as we improve the simplifier. -/
@[simp] lemma lt_ne_eq : ordering.lt ≠ ordering.eq :=
by contradiction

@[simp] lemma lt_ne_gt : ordering.lt ≠ ordering.gt :=
by contradiction

@[simp] lemma eq_ne_lt : ordering.eq ≠ ordering.lt :=
by contradiction

@[simp] lemma eq_ne_gt : ordering.eq ≠ ordering.gt :=
by contradiction

@[simp] lemma gt_ne_lt : ordering.gt ≠ ordering.lt :=
by contradiction

@[simp] lemma gt_ne_eq : ordering.gt ≠ ordering.eq :=
by contradiction

@[simp] theorem ite_eq_lt_distrib (c : Prop) [decidable c] (a b : ordering) : ((if c then a else b) = ordering.lt) = (if c then a = ordering.lt else b = ordering.lt) :=
by by_cases c with h; simp [h]

@[simp] theorem ite_eq_eq_distrib (c : Prop) [decidable c] (a b : ordering) : ((if c then a else b) = ordering.eq) = (if c then a = ordering.eq else b = ordering.eq) :=
by by_cases c with h; simp [h]

@[simp] theorem ite_eq_gt_distrib (c : Prop) [decidable c] (a b : ordering) : ((if c then a else b) = ordering.gt) = (if c then a = ordering.gt else b = ordering.gt) :=
by by_cases c with h; simp [h]

/- ------------------------------------------------------------------ -/
end ordering

section
variables {α : Type u} [has_lt α] [decidable_rel ((<) : α → α → Prop)]

@[simp] lemma cmp_eq_lt (a b : α) : (cmp a b = ordering.lt) = (a < b) :=
by simp [cmp]

@[simp] lemma cmp_eq_gt [is_strict_order α ((<) : α → α → Prop)] (a b : α) : (cmp a b = ordering.gt) = (b < a) :=
begin
  simp [cmp], apply propext, apply iff.intro,
  { exact λ h, h.1 },
  { intro hba, split, assumption, intro hab, exact absurd (trans hab hba) (irrefl a) }
end

@[simp] lemma cmp_eq_eq (a b : α) : (cmp a b = ordering.eq) = (¬ a < b ∧ ¬ b < a) :=
by simp [cmp]

lemma lt_of_cmp_eq_lt (a b : α) : cmp a b = ordering.lt → a < b :=
eq.mp (cmp_eq_lt a b)

lemma gt_of_cmp_eq_gt (a b : α) : cmp a b = ordering.gt → b < a :=
begin simp [cmp], intro h, exact h.1 end

lemma incomp_of_cmp_eq_eq (a b : α) : cmp a b = ordering.eq → ¬ a < b ∧ ¬ b < a :=
eq.mp (cmp_eq_eq a b)
end
