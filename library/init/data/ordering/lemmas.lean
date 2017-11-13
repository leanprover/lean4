/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.ordering.basic init.meta init.algebra.classes
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

class has_strict_weak_ordering (α : Type u) extends has_cmp α, is_strict_weak_order α (<_cmp) :=
(lt_iff_gt     : ∀ a b : α, a <_cmp b     ↔ b >_cmp a)
(incomp_iff_eq : ∀ a b : α, a ≈[cmp_lt] b ↔ a =_cmp b)

namespace ordering
variables {α : Type u} [has_strict_weak_ordering α]
open strict_weak_order

lemma cmp_lt_of_cmp_gt {a b : α} : a >_cmp b → b <_cmp a :=
λ h, iff.mpr (has_strict_weak_ordering.lt_iff_gt b a) h

private lemma to_eq {a b : α} : a ≈[cmp_lt] b → a =_cmp b :=
iff.mp (has_strict_weak_ordering.incomp_iff_eq a b)

private lemma to_eqv {a b : α} : a =_cmp b → a ≈[cmp_lt] b :=
iff.mpr (has_strict_weak_ordering.incomp_iff_eq a b)

instance : is_equiv α (=_cmp) :=
{refl  := λ a, to_eq (erefl a),
 symm  := λ a b h, to_eq (esymm (to_eqv h)),
 trans := λ a c c h₁ h₂, to_eq (etrans (to_eqv h₁) (to_eqv h₂))}

lemma eqv_of_incomparable {a b : α} : ¬ a <_cmp b → ¬ b <_cmp a → a ≈[cmp_lt] b :=
λ h₁ h₂, ⟨h₁, h₂⟩
end ordering
