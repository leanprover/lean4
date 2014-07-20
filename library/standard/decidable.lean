-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import logic

namespace decidable
inductive decidable (p : Bool) : Type :=
| inl : p  → decidable p
| inr : ¬p → decidable p

theorem induction_on {p : Bool} {C : Bool} (H : decidable p) (H1 : p → C) (H2 : ¬p → C) : C
:= decidable_rec H1 H2 H

theorem em (p : Bool) (H : decidable p) : p ∨ ¬p
:= induction_on H (λ Hp, or_intro_left _ Hp) (λ Hnp, or_intro_right _ Hnp)

definition rec [inline] {p : Bool} {C : Type} (H : decidable p) (H1 : p → C) (H2 : ¬p → C) : C
:= decidable_rec H1 H2 H

theorem decidable_true [instance] : decidable true
:= inl trivial

theorem decidable_false [instance] : decidable false
:= inr not_false_trivial

theorem decidable_and [instance] {a b : Bool} (Ha : decidable a) (Hb : decidable b) : decidable (a ∧ b)
:= rec Ha
    (assume Ha  : a, rec Hb
      (assume Hb  : b,  inl (and_intro Ha Hb))
      (assume Hnb : ¬b, inr (and_not_right a Hnb)))
    (assume Hna : ¬a, inr (and_not_left b Hna))

theorem decidable_or [instance] {a b : Bool} (Ha : decidable a) (Hb : decidable b) : decidable (a ∨ b)
:= rec Ha
    (assume Ha  : a, inl (or_intro_left b Ha))
    (assume Hna : ¬a, rec Hb
      (assume Hb  : b,  inl (or_intro_right a Hb))
      (assume Hnb : ¬b, inr (or_not_intro Hna Hnb)))

theorem decidable_not [instance] {a : Bool} (Ha : decidable a) : decidable (¬a)
:= rec Ha
    (assume Ha,  inr (not_not_intro Ha))
    (assume Hna, inl Hna)

theorem decidable_iff [instance] {a b : Bool} (Ha : decidable a) (Hb : decidable b) : decidable (a ↔ b)
:= rec Ha
    (assume Ha, rec Hb
      (assume Hb  : b,  inl (iff_intro (assume H, Hb) (assume H, Ha)))
      (assume Hnb : ¬b, inr (not_intro (assume H : a ↔ b, absurd (iff_mp_left H Ha) Hnb))))
    (assume Hna, rec Hb
      (assume Hb  : b,  inr (not_intro (assume H : a ↔ b, absurd (iff_mp_right H Hb) Hna)))
      (assume Hnb : ¬b, inl (iff_intro (assume Ha, absurd_elim b Ha Hna) (assume Hb, absurd_elim a Hb Hnb))))

theorem decidable_implies [instance] {a b : Bool} (Ha : decidable a) (Hb : decidable b) : decidable (a → b)
:= rec Ha
    (assume Ha  : a, rec Hb
      (assume Hb  : b,  inl (assume H, Hb))
      (assume Hnb : ¬b, inr (not_intro (assume H : a → b,
        absurd (H Ha) Hnb))))
    (assume Hna : ¬a, inl (assume Ha, absurd_elim b Ha Hna))
