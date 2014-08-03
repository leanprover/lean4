----------------------------------------------------------------------------------------------------
-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
----------------------------------------------------------------------------------------------------

import logic.connectives.basic logic.connectives.eq

namespace decidable

inductive decidable (p : Prop) : Type :=
| inl : p  → decidable p
| inr : ¬p → decidable p

theorem induction_on {p : Prop} {C : Prop} (H : decidable p) (H1 : p → C) (H2 : ¬p → C) : C :=
decidable_rec H1 H2 H

theorem em {p : Prop} (H : decidable p) : p ∨ ¬p :=
induction_on H (λ Hp, or_inl Hp) (λ Hnp, or_inr Hnp)

definition rec_on [inline] {p : Prop} {C : Type} (H : decidable p) (H1 : p → C) (H2 : ¬p → C) : C :=
decidable_rec H1 H2 H

theorem irrelevant {p : Prop} (d1 d2 : decidable p) : d1 = d2 :=
decidable_rec
  (assume Hp1 : p, decidable_rec
    (assume Hp2  : p,  congr2 inl (refl Hp1)) -- using proof irrelevance for Prop
    (assume Hnp2 : ¬p, absurd_elim (inl Hp1 = inr Hnp2) Hp1 Hnp2)
    d2)
  (assume Hnp1 : ¬p, decidable_rec
    (assume Hp2  : p,  absurd_elim (inr Hnp1 = inl Hp2) Hp2 Hnp1)
    (assume Hnp2 : ¬p, congr2 inr (refl Hnp1)) -- using proof irrelevance for Prop
    d2)
  d1

theorem decidable_true [instance] : decidable true :=
inl trivial

theorem decidable_false [instance] : decidable false :=
inr not_false_trivial

theorem decidable_and [instance] {a b : Prop} (Ha : decidable a) (Hb : decidable b) : decidable (a ∧ b) :=
rec_on Ha
  (assume Ha  : a, rec_on Hb
    (assume Hb  : b,  inl (and_intro Ha Hb))
    (assume Hnb : ¬b, inr (and_not_right a Hnb)))
  (assume Hna : ¬a, inr (and_not_left b Hna))

theorem decidable_or [instance] {a b : Prop} (Ha : decidable a) (Hb : decidable b) : decidable (a ∨ b) :=
rec_on Ha
  (assume Ha  : a, inl (or_inl Ha))
  (assume Hna : ¬a, rec_on Hb
    (assume Hb  : b,  inl (or_inr Hb))
    (assume Hnb : ¬b, inr (or_not_intro Hna Hnb)))

theorem decidable_not [instance] {a : Prop} (Ha : decidable a) : decidable (¬a) :=
rec_on Ha
  (assume Ha,  inr (not_not_intro Ha))
  (assume Hna, inl Hna)

theorem decidable_iff [instance] {a b : Prop} (Ha : decidable a) (Hb : decidable b) : decidable (a ↔ b) :=
rec_on Ha
  (assume Ha, rec_on Hb
    (assume Hb  : b,  inl (iff_intro (assume H, Hb) (assume H, Ha)))
    (assume Hnb : ¬b, inr (assume H : a ↔ b, absurd (iff_elim_left H Ha) Hnb)))
  (assume Hna, rec_on Hb
    (assume Hb  : b,  inr (assume H : a ↔ b, absurd (iff_elim_right H Hb) Hna))
    (assume Hnb : ¬b, inl (iff_intro (assume Ha, absurd_elim b Ha Hna) (assume Hb, absurd_elim a Hb Hnb))))

theorem decidable_implies [instance] {a b : Prop} (Ha : decidable a) (Hb : decidable b) : decidable (a → b) :=
rec_on Ha
  (assume Ha  : a, rec_on Hb
    (assume Hb  : b,  inl (assume H, Hb))
    (assume Hnb : ¬b, inr (assume H : a → b, absurd (H Ha) Hnb)))
  (assume Hna : ¬a, inl (assume Ha, absurd_elim b Ha Hna))

end