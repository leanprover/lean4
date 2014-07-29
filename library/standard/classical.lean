-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import logic cast
using eq_proofs

axiom prop_complete (a : Prop) : a = true ∨ a = false

theorem case (P : Prop → Prop) (H1 : P true) (H2 : P false) (a : Prop) : P a :=
or_elim (prop_complete a)
  (assume Ht : a = true,  Ht⁻¹ ▸ H1)
  (assume Hf : a = false, Hf⁻¹ ▸ H2)

theorem em (a : Prop) : a ∨ ¬a :=
or_elim (prop_complete a)
  (assume Ht : a = true,  or_inl (eqt_elim Ht))
  (assume Hf : a = false, or_inr (eqf_elim Hf))

theorem prop_complete_swapped (a : Prop) : a = false ∨ a = true :=
case (λ x, x = false ∨ x = true)
  (or_inr (refl true))
  (or_inl (refl false))
  a

theorem not_true : (¬true) = false :=
have aux : (¬true) ≠ true, from
  assume H : (¬true) = true,
    absurd_not_true (H⁻¹ ▸ trivial),
resolve_right (prop_complete (¬true)) aux

theorem not_false : (¬false) = true :=
have aux : (¬false) ≠ false, from
  assume H : (¬false) = false,
    H ▸ not_false_trivial,
resolve_right (prop_complete_swapped (¬false)) aux

theorem not_not_eq (a : Prop) : (¬¬a) = a :=
case (λ x, (¬¬x) = x)
  (calc (¬¬true)  = (¬false) : {not_true}
            ...   = true     : not_false)
  (calc (¬¬false) = (¬true)  : {not_false}
            ...   = false    : not_true)
  a

theorem not_not_elim {a : Prop} (H : ¬¬a) : a :=
(not_not_eq a) ◂ H

theorem propext {a b : Prop} (Hab : a → b) (Hba : b → a) : a = b :=
or_elim (prop_complete a)
  (assume Hat,  or_elim (prop_complete b)
    (assume Hbt,  Hat ⬝ Hbt⁻¹)
    (assume Hbf, false_elim (a = b) (Hbf ▸ (Hab (eqt_elim Hat)))))
  (assume Haf, or_elim (prop_complete b)
    (assume Hbt,  false_elim (a = b) (Haf ▸ (Hba (eqt_elim Hbt))))
    (assume Hbf, Haf ⬝ Hbf⁻¹))

theorem iff_to_eq {a b : Prop} (H : a ↔ b) : a = b :=
iff_elim (assume H1 H2, propext H1 H2) H

theorem iff_eq_eq {a b : Prop} : (a ↔ b) = (a = b) :=
propext
  (assume H, iff_to_eq H)
  (assume H, eq_to_iff H)

theorem eqt_intro {a : Prop} (H : a) : a = true :=
propext
  (assume H1 : a,    trivial)
  (assume H2 : true, H)

theorem eqf_intro {a : Prop} (H : ¬a) : a = false :=
propext
  (assume H1 : a,     absurd H1 H)
  (assume H2 : false, false_elim a H2)

theorem by_contradiction {a : Prop} (H : ¬a → false) : a :=
or_elim (em a)
  (assume H1 : a, H1)
  (assume H1 : ¬a, false_elim a (H H1))

theorem a_neq_a {A : Type} (a : A) : (a ≠ a) = false :=
propext
  (assume H, a_neq_a_elim H)
  (assume H, false_elim (a ≠ a) H)

theorem eq_id {A : Type} (a : A) : (a = a) = true :=
eqt_intro (refl a)

theorem heq_id {A : Type} (a : A) : (a == a) = true :=
eqt_intro (hrefl a)

theorem not_or (a b : Prop) : (¬(a ∨ b)) = (¬a ∧ ¬b) :=
propext
  (assume H, or_elim (em a)
    (assume Ha, absurd_elim (¬a ∧ ¬b) (or_inl Ha) H)
    (assume Hna, or_elim (em b)
      (assume Hb, absurd_elim (¬a ∧ ¬b) (or_inr Hb) H)
      (assume Hnb, and_intro Hna Hnb)))
  (assume (H : ¬a ∧ ¬b) (N : a ∨ b),
    or_elim N
      (assume Ha, absurd Ha (and_elim_left H))
      (assume Hb, absurd Hb (and_elim_right H)))

theorem not_and (a b : Prop) : (¬(a ∧ b)) = (¬a ∨ ¬b) :=
propext
  (assume H, or_elim (em a)
    (assume Ha, or_elim (em b)
      (assume Hb, absurd_elim (¬a ∨ ¬b) (and_intro Ha Hb) H)
      (assume Hnb, or_inr Hnb))
    (assume Hna, or_inl Hna))
  (assume (H : ¬a ∨ ¬b) (N : a ∧ b),
    or_elim H
      (assume Hna, absurd (and_elim_left N) Hna)
      (assume Hnb, absurd (and_elim_right N) Hnb))

theorem imp_or (a b : Prop) : (a → b) = (¬a ∨ b) :=
propext
  (assume H : a → b, (or_elim (em a)
    (assume Ha  : a,   or_inr (H Ha))
    (assume Hna : ¬a, or_inl Hna)))
  (assume (H : ¬a ∨ b) (Ha : a),
    resolve_right H ((not_not_eq a)⁻¹ ◂ Ha))

theorem not_implies (a b : Prop) : (¬(a → b)) = (a ∧ ¬b) :=
calc (¬(a → b)) = (¬(¬a ∨ b)) : {imp_or a b}
            ... = (¬¬a ∧ ¬b)  : not_or (¬a) b
            ... = (a ∧ ¬b)    : {not_not_eq a}

theorem a_eq_not_a (a : Prop) : (a = ¬a) = false :=
propext
  (assume H, or_elim (em a)
    (assume Ha, absurd Ha (H ▸ Ha))
    (assume Hna, absurd (H⁻¹ ▸ Hna) Hna))
  (assume H, false_elim (a = ¬a) H)

theorem true_eq_false : (true = false) = false :=
not_true ▸ (a_eq_not_a true)

theorem false_eq_true : (false = true) = false :=
not_false ▸ (a_eq_not_a false)

theorem a_eq_true (a : Prop) : (a = true) = a :=
propext (assume H, eqt_elim H) (assume H, eqt_intro H)

theorem a_eq_false (a : Prop) : (a = false) = ¬a :=
propext (assume H, eqf_elim H) (assume H, eqf_intro H)

theorem not_exists_forall {A : Type} {P : A → Prop} (H : ¬∃x, P x) : ∀x, ¬P x :=
take x, or_elim (em (P x))
  (assume Hp : P x,   absurd_elim (¬P x) (exists_intro x Hp) H)
  (assume Hn : ¬P x, Hn)

theorem not_forall_exists {A : Type} {P : A → Prop} (H : ¬∀x, P x) : ∃x, ¬P x :=
by_contradiction (assume H1 : ¬∃ x, ¬P x,
  have H2 : ∀x, ¬¬P x, from not_exists_forall H1,
  have H3 : ∀x, P x, from take x, not_not_elim (H2 x),
  absurd H3 H)

theorem peirce (a b : Prop) : ((a → b) → a) → a :=
assume H, by_contradiction (assume Hna : ¬a,
  have Hnna : ¬¬a, from not_implies_left (mt H Hna),
  absurd (not_not_elim Hnna) Hna)
