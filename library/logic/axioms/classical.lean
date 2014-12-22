/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: logic.axioms.classical
Author: Leonardo de Moura
-/

import logic.connectives logic.quantifiers logic.cast algebra.relation

open eq.ops

axiom prop_complete (a : Prop) : a = true ∨ a = false

definition eq_true_or_eq_false := prop_complete

theorem cases (P : Prop → Prop) (H1 : P true) (H2 : P false) (a : Prop) : P a :=
or.elim (prop_complete a)
  (assume Ht : a = true,  Ht⁻¹ ▸ H1)
  (assume Hf : a = false, Hf⁻¹ ▸ H2)

theorem cases_on (a : Prop) {P : Prop → Prop} (H1 : P true) (H2 : P false) : P a :=
cases P H1 H2 a

-- this supercedes the em in decidable
theorem em (a : Prop) : a ∨ ¬a :=
or.elim (prop_complete a)
  (assume Ht : a = true,  or.inl (of_eq_true Ht))
  (assume Hf : a = false, or.inr (not_of_eq_false Hf))

theorem eq_false_or_eq_true (a : Prop) : a = false ∨ a = true :=
cases (λ x, x = false ∨ x = true)
  (or.inr rfl)
  (or.inl rfl)
  a

theorem propext {a b : Prop} (Hab : a → b) (Hba : b → a) : a = b :=
or.elim (prop_complete a)
  (assume Hat,  or.elim (prop_complete b)
    (assume Hbt,  Hat ⬝ Hbt⁻¹)
    (assume Hbf, false.elim (Hbf ▸ (Hab (of_eq_true Hat)))))
  (assume Haf, or.elim (prop_complete b)
    (assume Hbt,  false.elim (Haf ▸ (Hba (of_eq_true Hbt))))
    (assume Hbf, Haf ⬝ Hbf⁻¹))

theorem eq.of_iff {a b : Prop} (H : a ↔ b) : a = b :=
iff.elim (assume H1 H2, propext H1 H2) H

theorem iff_eq_eq {a b : Prop} : (a ↔ b) = (a = b) :=
propext
  (assume H, eq.of_iff H)
  (assume H, iff.of_eq H)

open relation
theorem iff_congruence [instance] (P : Prop → Prop) : is_congruence iff iff P :=
is_congruence.mk
  (take (a b : Prop),
    assume H : a ↔ b,
    show P a ↔ P b, from iff.of_eq (eq.of_iff H ▸ eq.refl (P a)))
