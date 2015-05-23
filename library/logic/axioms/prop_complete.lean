/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import logic.connectives logic.quantifiers logic.cast algebra.relation
import logic.axioms.em
open eq.ops

theorem prop_complete (a : Prop) : a = true ∨ a = false :=
or.elim (em a)
  (λ t, or.inl (propext (iff.intro (λ h, trivial) (λ h, t))))
  (λ f, or.inr (propext (iff.intro (λ h, absurd h f) (λ h, false.elim h))))

definition eq_true_or_eq_false := prop_complete

theorem cases_true_false (P : Prop → Prop) (H1 : P true) (H2 : P false) (a : Prop) : P a :=
or.elim (prop_complete a)
  (assume Ht : a = true,  Ht⁻¹ ▸ H1)
  (assume Hf : a = false, Hf⁻¹ ▸ H2)

theorem cases_on (a : Prop) {P : Prop → Prop} (H1 : P true) (H2 : P false) : P a :=
cases_true_false P H1 H2 a

-- this supercedes by_cases in decidable
definition by_cases {p q : Prop} (Hpq : p → q) (Hnpq : ¬p → q) : q :=
or.elim (em p) (assume Hp, Hpq Hp) (assume Hnp, Hnpq Hnp)

-- this supercedes by_contradiction in decidable
theorem by_contradiction {p : Prop} (H : ¬p → false) : p :=
by_cases
  (assume H1 : p, H1)
  (assume H1 : ¬p, false.rec _ (H H1))

theorem eq_false_or_eq_true (a : Prop) : a = false ∨ a = true :=
cases_true_false (λ x, x = false ∨ x = true)
  (or.inr rfl)
  (or.inl rfl)
  a

theorem eq.of_iff {a b : Prop} (H : a ↔ b) : a = b :=
iff.elim (assume H1 H2, propext (iff.intro H1 H2)) H

theorem iff_eq_eq {a b : Prop} : (a ↔ b) = (a = b) :=
propext (iff.intro
  (assume H, eq.of_iff H)
  (assume H, iff.of_eq H))

open relation
theorem iff_congruence [instance] (P : Prop → Prop) : is_congruence iff iff P :=
is_congruence.mk
  (take (a b : Prop),
    assume H : a ↔ b,
    show P a ↔ P b, from iff.of_eq (eq.of_iff H ▸ eq.refl (P a)))
