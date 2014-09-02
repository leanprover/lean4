-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura

import logic.core.connectives

namespace decidable

inductive decidable (p : Prop) : Type :=
inl : p  → decidable p,
inr : ¬p → decidable p

theorem true_decidable [instance] : decidable true :=
inl trivial

theorem false_decidable [instance] : decidable false :=
inr not_false_trivial

theorem induction_on {p : Prop} {C : Prop} (H : decidable p) (H1 : p → C) (H2 : ¬p → C) : C :=
decidable_rec H1 H2 H

definition rec_on [inline] {p : Prop} {C : Type} (H : decidable p) (H1 : p → C) (H2 : ¬p → C) :
  C :=
decidable_rec H1 H2 H

theorem irrelevant {p : Prop} (d1 d2 : decidable p) : d1 = d2 :=
decidable_rec
  (assume Hp1 : p, decidable_rec
    (assume Hp2  : p,  congr_arg inl (refl Hp1)) -- using proof irrelevance for Prop
    (assume Hnp2 : ¬p, absurd Hp1 Hnp2)
    d2)
  (assume Hnp1 : ¬p, decidable_rec
    (assume Hp2  : p,  absurd Hp2 Hnp1)
    (assume Hnp2 : ¬p, congr_arg inr (refl Hnp1)) -- using proof irrelevance for Prop
    d2)
  d1

theorem em (p : Prop) {H : decidable p} : p ∨ ¬p :=
induction_on H (λ Hp, or_inl Hp) (λ Hnp, or_inr Hnp)

theorem by_cases {a b : Prop} {C : decidable a} (Hab : a → b) (Hnab : ¬a → b) : b :=
or_elim (em a) (assume Ha, Hab Ha) (assume Hna, Hnab Hna)

theorem by_contradiction {p : Prop} {Hp : decidable p} (H : ¬p → false) : p :=
or_elim (em p)
  (assume H1 : p, H1)
  (assume H1 : ¬p, false_elim (H H1))

theorem and_decidable [instance] {a b : Prop} (Ha : decidable a) (Hb : decidable b) :
  decidable (a ∧ b) :=
rec_on Ha
  (assume Ha  : a, rec_on Hb
    (assume Hb  : b,  inl (and_intro Ha Hb))
    (assume Hnb : ¬b, inr (and_not_right a Hnb)))
  (assume Hna : ¬a, inr (and_not_left b Hna))

theorem or_decidable [instance] {a b : Prop} (Ha : decidable a) (Hb : decidable b) :
  decidable (a ∨ b) :=
rec_on Ha
  (assume Ha  : a, inl (or_inl Ha))
  (assume Hna : ¬a, rec_on Hb
    (assume Hb  : b,  inl (or_inr Hb))
    (assume Hnb : ¬b, inr (or_not_intro Hna Hnb)))

theorem not_decidable [instance] {a : Prop} (Ha : decidable a) : decidable (¬a) :=
rec_on Ha
  (assume Ha,  inr (not_not_intro Ha))
  (assume Hna, inl Hna)

theorem iff_decidable [instance] {a b : Prop} (Ha : decidable a) (Hb : decidable b) :
  decidable (a ↔ b) :=
rec_on Ha
  (assume Ha, rec_on Hb
    (assume Hb  : b,  inl (iff_intro (assume H, Hb) (assume H, Ha)))
    (assume Hnb : ¬b, inr (assume H : a ↔ b, absurd (iff_elim_left H Ha) Hnb)))
  (assume Hna, rec_on Hb
    (assume Hb  : b,  inr (assume H : a ↔ b, absurd (iff_elim_right H Hb) Hna))
    (assume Hnb : ¬b, inl
        (iff_intro (assume Ha, absurd Ha Hna) (assume Hb, absurd Hb Hnb))))

theorem implies_decidable [instance] {a b : Prop} (Ha : decidable a) (Hb : decidable b) :
  decidable (a → b) :=
rec_on Ha
  (assume Ha  : a, rec_on Hb
    (assume Hb  : b,  inl (assume H, Hb))
    (assume Hnb : ¬b, inr (assume H : a → b, absurd (H Ha) Hnb)))
  (assume Hna : ¬a, inl (assume Ha, absurd Ha Hna))

theorem decidable_iff_equiv {a b : Prop} (Ha : decidable a) (H : a ↔ b) : decidable b :=
rec_on Ha
  (assume Ha : a,   inl (iff_elim_left H Ha))
  (assume Hna : ¬a, inr (iff_elim_left (iff_flip_sign H) Hna))

theorem decidable_eq_equiv {a b : Prop} (Ha : decidable a) (H : a = b) : decidable b :=
decidable_iff_equiv Ha (eq_to_iff H)

end decidable
