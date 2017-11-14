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

instance cmp_of_lt_is_ordering {α : Type u} [has_lt α] [decidable_rel ((<) : α → α → Prop)] [h : is_strict_weak_order α ((<) : α → α → Prop)] : is_ordering α cmp_of_lt :=
{ trans         := by simp [cmp_of_lt]; exact h.trans,
  irrefl        := by simp [cmp_of_lt]; exact h.irrefl,
  incomp_trans  := by simp [cmp_of_lt]; exact h.incomp_trans,
  gt_iff_lt     :=
  begin
    simp [cmp_of_lt], intros, apply iff.intro,
    { intro h, exact h.1 },
    { intro h, split,
       { assumption },
       { intro h₁, apply irrefl _ (trans h h₁) } }
  end,
  eq_iff_incomp := by simp [cmp_of_lt]; intros; trivial
}

instance default_cmp_is_ordering {α : Type u} [has_lt α] [decidable_rel ((<) : α → α → Prop)] [is_strict_weak_order α ((<) : α → α → Prop)] : is_ordering α (@cmp α has_cmp_of_lt) :=
cmp_of_lt_is_ordering
