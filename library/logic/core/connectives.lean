-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Leonardo de Moura, Jeremy Avigad

import general_notation .eq

-- and
-- ---
inductive and (a b : Prop) : Prop :=
  intro : a → b → and a b

infixr `/\` := and
infixr `∧` := and

namespace and
  theorem elim {a b c : Prop} (H1 : a ∧ b) (H2 : a → b → c) : c :=
  rec H2 H1

  theorem elim_left {a b : Prop} (H : a ∧ b) : a  :=
  rec (λa b, a) H

  theorem elim_right {a b : Prop} (H : a ∧ b) : b :=
  rec (λa b, b) H

  theorem swap {a b : Prop} (H : a ∧ b) : b ∧ a :=
  intro (elim_right H) (elim_left H)

  theorem not_left {a : Prop} (b : Prop) (Hna : ¬a) : ¬(a ∧ b) :=
  assume H : a ∧ b, absurd (elim_left H) Hna

  theorem not_right (a : Prop) {b : Prop} (Hnb : ¬b) : ¬(a ∧ b) :=
  assume H : a ∧ b, absurd (elim_right H) Hnb

  theorem imp_and {a b c d : Prop} (H1 : a ∧ b) (H2 : a → c) (H3 : b → d) : c ∧ d :=
  elim H1 (assume Ha : a, assume Hb : b, intro (H2 Ha) (H3 Hb))

  theorem imp_left {a b c : Prop} (H1 : a ∧ c) (H : a → b) : b ∧ c :=
  elim H1 (assume Ha : a, assume Hc : c, intro (H Ha) Hc)

  theorem imp_right {a b c : Prop} (H1 : c ∧ a) (H : a → b) : c ∧ b :=
  elim H1 (assume Hc : c, assume Ha : a, intro Hc (H Ha))
end and

-- or
-- --
inductive or (a b : Prop) : Prop :=
  intro_left  : a → or a b,
  intro_right : b → or a b

infixr `\/` := or
infixr `∨` := or

namespace or
  theorem inl {a b : Prop} (Ha : a) : a ∨ b :=
  intro_left b Ha

  theorem inr {a b : Prop} (Hb : b) : a ∨ b :=
  intro_right a Hb

  theorem elim {a b c : Prop} (H1 : a ∨ b) (H2 : a → c) (H3 : b → c) : c :=
  rec H2 H3 H1

  theorem elim3 {a b c d : Prop} (H : a ∨ b ∨ c) (Ha : a → d) (Hb : b → d) (Hc : c → d) : d :=
  elim H Ha (assume H2, elim H2 Hb Hc)

  theorem resolve_right {a b : Prop} (H1 : a ∨ b) (H2 : ¬a) : b :=
  elim H1 (assume Ha, absurd Ha H2) (assume Hb, Hb)

  theorem resolve_left {a b : Prop} (H1 : a ∨ b) (H2 : ¬b) : a :=
  elim H1 (assume Ha, Ha) (assume Hb, absurd Hb H2)

  theorem swap {a b : Prop} (H : a ∨ b) : b ∨ a :=
  elim H (assume Ha, inr Ha) (assume Hb, inl Hb)

  theorem not_intro {a b : Prop} (Hna : ¬a) (Hnb : ¬b) : ¬(a ∨ b) :=
  assume H : a ∨ b, elim H
    (assume Ha, absurd Ha Hna)
    (assume Hb, absurd Hb Hnb)

  theorem imp_or {a b c d : Prop} (H1 : a ∨ b) (H2 : a → c) (H3 : b → d) : c ∨ d :=
  elim H1
    (assume Ha : a, inl (H2 Ha))
    (assume Hb : b, inr (H3 Hb))

  theorem imp_or_left {a b c : Prop} (H1 : a ∨ c) (H : a → b) : b ∨ c :=
  elim H1
    (assume H2 : a, inl (H H2))
    (assume H2 : c, inr H2)

  theorem imp_or_right {a b c : Prop} (H1 : c ∨ a) (H : a → b) : c ∨ b :=
  elim H1
    (assume H2 : c, inl H2)
    (assume H2 : a, inr (H H2))
end or

theorem not_not_em {p : Prop} : ¬¬(p ∨ ¬p) :=
assume not_em : ¬(p ∨ ¬p),
  have Hnp : ¬p, from
    assume Hp : p, absurd (or.inl Hp) not_em,
  absurd (or.inr Hnp) not_em

-- iff
-- ---
definition iff (a b : Prop) := (a → b) ∧ (b → a)

infix `<->` := iff
infix `↔` := iff

namespace iff
  theorem def {a b : Prop} : (a ↔ b) = ((a → b) ∧ (b → a)) :=
  rfl

  theorem intro {a b : Prop} (H1 : a → b) (H2 : b → a) : a ↔ b :=
  and.intro H1 H2

  theorem elim {a b c : Prop} (H1 : (a → b) → (b → a) → c) (H2 : a ↔ b) : c :=
  and.rec H1 H2

  theorem elim_left {a b : Prop} (H : a ↔ b) : a → b :=
  elim (assume H1 H2, H1) H

  abbreviation mp := @elim_left

  theorem elim_right {a b : Prop} (H : a ↔ b) : b → a :=
  elim (assume H1 H2, H2) H

  theorem flip_sign {a b : Prop} (H1 : a ↔ b) : ¬a ↔ ¬b :=
  intro
    (assume Hna, mt (elim_right H1) Hna)
    (assume Hnb, mt (elim_left H1) Hnb)

  theorem refl (a : Prop) : a ↔ a :=
  intro (assume H, H) (assume H, H)

  theorem rfl {a : Prop} : a ↔ a :=
  refl a

  theorem trans {a b c : Prop} (H1 : a ↔ b) (H2 : b ↔ c) : a ↔ c :=
  intro
    (assume Ha, elim_left H2 (elim_left H1 Ha))
    (assume Hc, elim_right H1 (elim_right H2 Hc))

  theorem symm {a b : Prop} (H : a ↔ b) : b ↔ a :=
  intro
    (assume Hb, elim_right H Hb)
    (assume Ha, elim_left H Ha)

  theorem true_elim {a : Prop} (H : a ↔ true) : a :=
  mp (symm H) trivial

  theorem false_elim {a : Prop} (H : a ↔ false) : ¬a :=
  assume Ha : a, mp H Ha
end iff

calc_refl iff.refl
calc_trans iff.trans

open eq_ops

theorem eq_to_iff {a b : Prop} (H : a = b) : a ↔ b :=
iff.intro (λ Ha, H ▸ Ha) (λ Hb, H⁻¹ ▸ Hb)

-- comm and assoc for and / or
-- ---------------------------

namespace and
  theorem comm {a b : Prop} : a ∧ b ↔ b ∧ a :=
  iff.intro (λH, swap H) (λH, swap H)

  theorem assoc {a b c : Prop} : (a ∧ b) ∧ c ↔ a ∧ (b ∧ c) :=
  iff.intro
    (assume H, intro
      (elim_left (elim_left H))
      (intro (elim_right (elim_left H)) (elim_right H)))
    (assume H, intro
      (intro (elim_left H) (elim_left (elim_right H)))
      (elim_right (elim_right H)))
end and

namespace or
  theorem comm {a b : Prop} : a ∨ b ↔ b ∨ a :=
  iff.intro (λH, swap H) (λH, swap H)

  theorem assoc {a b c : Prop} : (a ∨ b) ∨ c ↔ a ∨ (b ∨ c) :=
  iff.intro
    (assume H, elim H
      (assume H1, elim H1
        (assume Ha, inl Ha)
        (assume Hb, inr (inl Hb)))
      (assume Hc, inr (inr Hc)))
    (assume H, elim H
      (assume Ha, (inl (inl Ha)))
      (assume H1, elim H1
        (assume Hb, inl (inr Hb))
        (assume Hc, inr Hc)))
end or
