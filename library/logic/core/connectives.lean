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

theorem or_inl {a b : Prop} (Ha : a) : a ∨ b := or.intro_left b Ha
theorem or_inr {a b : Prop} (Hb : b) : a ∨ b := or.intro_right a Hb

theorem or_elim {a b c : Prop} (H1 : a ∨ b) (H2 : a → c) (H3 : b → c) : c :=
or.rec H2 H3 H1

theorem resolve_right {a b : Prop} (H1 : a ∨ b) (H2 : ¬a) : b :=
or_elim H1 (assume Ha, absurd Ha H2) (assume Hb, Hb)

theorem resolve_left {a b : Prop} (H1 : a ∨ b) (H2 : ¬b) : a :=
or_elim H1 (assume Ha, Ha) (assume Hb, absurd Hb H2)

theorem or_swap {a b : Prop} (H : a ∨ b) : b ∨ a :=
or_elim H (assume Ha, or_inr Ha) (assume Hb, or_inl Hb)

theorem or_not_intro {a b : Prop} (Hna : ¬a) (Hnb : ¬b) : ¬(a ∨ b) :=
assume H : a ∨ b, or_elim H
  (assume Ha, absurd Ha Hna)
  (assume Hb, absurd Hb Hnb)

theorem or_imp_or {a b c d : Prop} (H1 : a ∨ b) (H2 : a → c) (H3 : b → d) : c ∨ d :=
or_elim H1
  (assume Ha : a, or_inl (H2 Ha))
  (assume Hb : b, or_inr (H3 Hb))

theorem or_imp_or_left {a b c : Prop} (H1 : a ∨ c) (H : a → b) : b ∨ c :=
or_elim H1
  (assume H2 : a, or_inl (H H2))
  (assume H2 : c, or_inr H2)

theorem or_imp_or_right {a b c : Prop} (H1 : c ∨ a) (H : a → b) : c ∨ b :=
or_elim H1
  (assume H2 : c, or_inl H2)
  (assume H2 : a, or_inr (H H2))

theorem not_not_em {p : Prop} : ¬¬(p ∨ ¬p) :=
assume not_em : ¬(p ∨ ¬p),
  have Hnp : ¬p, from
    assume Hp : p, absurd (or_inl Hp) not_em,
  absurd (or_inr Hnp) not_em

-- iff
-- ---

definition iff (a b : Prop) := (a → b) ∧ (b → a)
infix `<->` := iff
infix `↔` := iff

theorem iff_def {a b : Prop} : (a ↔ b) = ((a → b) ∧ (b → a)) := rfl

theorem iff_intro {a b : Prop} (H1 : a → b) (H2 : b → a) : a ↔ b := and.intro H1 H2

theorem iff_elim {a b c : Prop} (H1 : (a → b) → (b → a) → c) (H2 : a ↔ b) : c := and.rec H1 H2

theorem iff_elim_left {a b : Prop} (H : a ↔ b) : a → b :=
iff_elim (assume H1 H2, H1) H

abbreviation iff_mp := @iff_elim_left

theorem iff_elim_right {a b : Prop} (H : a ↔ b) : b → a :=
iff_elim (assume H1 H2, H2) H

theorem iff_flip_sign {a b : Prop} (H1 : a ↔ b) : ¬a ↔ ¬b :=
iff_intro
  (assume Hna, mt (iff_elim_right H1) Hna)
  (assume Hnb, mt (iff_elim_left H1) Hnb)

theorem iff_refl (a : Prop) : a ↔ a :=
iff_intro (assume H, H) (assume H, H)

theorem iff_rfl {a : Prop} : a ↔ a :=
iff_refl a

theorem iff_trans {a b c : Prop} (H1 : a ↔ b) (H2 : b ↔ c) : a ↔ c :=
iff_intro
  (assume Ha, iff_elim_left H2 (iff_elim_left H1 Ha))
  (assume Hc, iff_elim_right H1 (iff_elim_right H2 Hc))

theorem iff_symm {a b : Prop} (H : a ↔ b) : b ↔ a :=
iff_intro
  (assume Hb, iff_elim_right H Hb)
  (assume Ha, iff_elim_left H Ha)

calc_refl iff_refl
calc_trans iff_trans

theorem iff_true_elim {a : Prop} (H : a ↔ true) : a :=
iff_mp (iff_symm H) trivial

theorem iff_false_elim {a : Prop} (H : a ↔ false) : ¬a :=
assume Ha : a, iff_mp H Ha

theorem eq_to_iff {a b : Prop} (H : a = b) : a ↔ b :=
iff_intro (λ Ha, subst H Ha) (λ Hb, subst (symm H) Hb)


-- comm and assoc for and / or
-- ---------------------------

theorem and_comm {a b : Prop} : a ∧ b ↔ b ∧ a :=
iff_intro (λH, and.swap H) (λH, and.swap H)

theorem and_assoc {a b c : Prop} : (a ∧ b) ∧ c ↔ a ∧ (b ∧ c) :=
iff_intro
  (assume H, and.intro
    (and.elim_left (and.elim_left H))
    (and.intro (and.elim_right (and.elim_left H)) (and.elim_right H)))
  (assume H, and.intro
    (and.intro (and.elim_left H) (and.elim_left (and.elim_right H)))
    (and.elim_right (and.elim_right H)))

theorem or_comm {a b : Prop} : a ∨ b ↔ b ∨ a :=
iff_intro (λH, or_swap H) (λH, or_swap H)

theorem or_assoc {a b c : Prop} : (a ∨ b) ∨ c ↔ a ∨ (b ∨ c) :=
iff_intro
  (assume H, or_elim H
    (assume H1, or_elim H1
      (assume Ha, or_inl Ha)
      (assume Hb, or_inr (or_inl Hb)))
    (assume Hc, or_inr (or_inr Hc)))
  (assume H, or_elim H
    (assume Ha, (or_inl (or_inl Ha)))
    (assume H1, or_elim H1
      (assume Hb, or_inl (or_inr Hb))
      (assume Hc, or_inr Hc)))
