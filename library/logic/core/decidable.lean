-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura

import logic.core.connectives

inductive decidable (p : Prop) : Type :=
inl : p  → decidable p,
inr : ¬p → decidable p

namespace decidable

definition true_decidable [instance] : decidable true :=
inl trivial

definition false_decidable [instance] : decidable false :=
inr not_false_trivial

protected theorem induction_on {p : Prop} {C : Prop} (H : decidable p) (H1 : p → C) (H2 : ¬p → C) : C :=
decidable.rec H1 H2 H

protected definition rec_on {p : Prop} {C : Type} (H : decidable p) (H1 : p → C) (H2 : ¬p → C) :
  C :=
decidable.rec H1 H2 H

theorem irrelevant {p : Prop} (d1 d2 : decidable p) : d1 = d2 :=
decidable.rec
  (assume Hp1 : p, decidable.rec
    (assume Hp2  : p,  congr_arg inl (eq.refl Hp1)) -- using proof irrelevance for Prop
    (assume Hnp2 : ¬p, absurd Hp1 Hnp2)
    d2)
  (assume Hnp1 : ¬p, decidable.rec
    (assume Hp2  : p,  absurd Hp2 Hnp1)
    (assume Hnp2 : ¬p, congr_arg inr (eq.refl Hnp1)) -- using proof irrelevance for Prop
    d2)
  d1

theorem em (p : Prop) {H : decidable p} : p ∨ ¬p :=
induction_on H (λ Hp, or.inl Hp) (λ Hnp, or.inr Hnp)

definition by_cases {a : Prop} {b : Type} {C : decidable a} (Hab : a → b) (Hnab : ¬a → b) : b :=
rec_on C (assume Ha, Hab Ha) (assume Hna, Hnab Hna)

theorem by_contradiction {p : Prop} {Hp : decidable p} (H : ¬p → false) : p :=
or.elim (em p)
  (assume H1 : p, H1)
  (assume H1 : ¬p, false_elim (H H1))

definition and_decidable [instance] {a b : Prop} (Ha : decidable a) (Hb : decidable b) :
  decidable (a ∧ b) :=
rec_on Ha
  (assume Ha  : a, rec_on Hb
    (assume Hb  : b,  inl (and.intro Ha Hb))
    (assume Hnb : ¬b, inr (and.not_right a Hnb)))
  (assume Hna : ¬a, inr (and.not_left b Hna))

definition or_decidable [instance] {a b : Prop} (Ha : decidable a) (Hb : decidable b) :
  decidable (a ∨ b) :=
rec_on Ha
  (assume Ha  : a, inl (or.inl Ha))
  (assume Hna : ¬a, rec_on Hb
    (assume Hb  : b,  inl (or.inr Hb))
    (assume Hnb : ¬b, inr (or.not_intro Hna Hnb)))

definition not_decidable [instance] {a : Prop} (Ha : decidable a) : decidable (¬a) :=
rec_on Ha
  (assume Ha,  inr (not_not_intro Ha))
  (assume Hna, inl Hna)

definition iff_decidable [instance] {a b : Prop} (Ha : decidable a) (Hb : decidable b) :
  decidable (a ↔ b) :=
rec_on Ha
  (assume Ha, rec_on Hb
    (assume Hb  : b,  inl (iff.intro (assume H, Hb) (assume H, Ha)))
    (assume Hnb : ¬b, inr (assume H : a ↔ b, absurd (iff.elim_left H Ha) Hnb)))
  (assume Hna, rec_on Hb
    (assume Hb  : b,  inr (assume H : a ↔ b, absurd (iff.elim_right H Hb) Hna))
    (assume Hnb : ¬b, inl
        (iff.intro (assume Ha, absurd Ha Hna) (assume Hb, absurd Hb Hnb))))

definition implies_decidable [instance] {a b : Prop} (Ha : decidable a) (Hb : decidable b) :
  decidable (a → b) :=
rec_on Ha
  (assume Ha  : a, rec_on Hb
    (assume Hb  : b,  inl (assume H, Hb))
    (assume Hnb : ¬b, inr (assume H : a → b, absurd (H Ha) Hnb)))
  (assume Hna : ¬a, inl (assume Ha, absurd Ha Hna))

definition decidable_iff_equiv {a b : Prop} (Ha : decidable a) (H : a ↔ b) : decidable b :=
rec_on Ha
  (assume Ha : a,   inl (iff.elim_left H Ha))
  (assume Hna : ¬a, inr (iff.elim_left (iff.flip_sign H) Hna))

definition decidable_eq_equiv {a b : Prop} (Ha : decidable a) (H : a = b) : decidable b :=
decidable_iff_equiv Ha (eq_to_iff H)

end decidable

definition decidable_eq (A : Type) := Π (a b : A), decidable (a = b)
