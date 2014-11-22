-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Leonardo de Moura, Jeremy Avigad

import general_notation .eq

-- and
-- ---
inductive and (a b : Prop) : Prop :=
intro : a → b → and a b

notation a /\ b := and a b
notation a ∧ b  := and a b

variables {a b c d : Prop}

namespace and
  theorem elim (H₁ : a ∧ b) (H₂ : a → b → c) : c :=
  rec H₂ H₁

  definition elim_left (H : a ∧ b) : a  :=
  rec (λa b, a) H

  definition elim_right (H : a ∧ b) : b :=
  rec (λa b, b) H

  theorem swap (H : a ∧ b) : b ∧ a :=
  intro (elim_right H) (elim_left H)

  definition not_left (b : Prop) (Hna : ¬a) : ¬(a ∧ b) :=
  assume H : a ∧ b, absurd (elim_left H) Hna

  definition not_right (a : Prop) {b : Prop} (Hnb : ¬b) : ¬(a ∧ b) :=
  assume H : a ∧ b, absurd (elim_right H) Hnb

  theorem imp_and (H₁ : a ∧ b) (H₂ : a → c) (H₃ : b → d) : c ∧ d :=
  elim H₁ (assume Ha : a, assume Hb : b, intro (H₂ Ha) (H₃ Hb))

  theorem imp_left (H₁ : a ∧ c) (H : a → b) : b ∧ c :=
  elim H₁ (assume Ha : a, assume Hc : c, intro (H Ha) Hc)

  theorem imp_right (H₁ : c ∧ a) (H : a → b) : c ∧ b :=
  elim H₁ (assume Hc : c, assume Ha : a, intro Hc (H Ha))
end and

-- or
-- --
inductive or (a b : Prop) : Prop :=
  intro_left  : a → or a b,
  intro_right : b → or a b

notation a `\/` b := or a b
notation a ∨ b := or a b

namespace or
  definition inl (Ha : a) : a ∨ b :=
  intro_left b Ha

  definition inr (Hb : b) : a ∨ b :=
  intro_right a Hb

  theorem elim (H₁ : a ∨ b) (H₂ : a → c) (H₃ : b → c) : c :=
  rec H₂ H₃ H₁

  theorem elim3 (H : a ∨ b ∨ c) (Ha : a → d) (Hb : b → d) (Hc : c → d) : d :=
  elim H Ha (assume H₂, elim H₂ Hb Hc)

  theorem resolve_right (H₁ : a ∨ b) (H₂ : ¬a) : b :=
  elim H₁ (assume Ha, absurd Ha H₂) (assume Hb, Hb)

  theorem resolve_left (H₁ : a ∨ b) (H₂ : ¬b) : a :=
  elim H₁ (assume Ha, Ha) (assume Hb, absurd Hb H₂)

  theorem swap (H : a ∨ b) : b ∨ a :=
  elim H (assume Ha, inr Ha) (assume Hb, inl Hb)

  definition not_intro (Hna : ¬a) (Hnb : ¬b) : ¬(a ∨ b) :=
  assume H : a ∨ b, or.rec_on H
    (assume Ha, absurd Ha Hna)
    (assume Hb, absurd Hb Hnb)

  theorem imp_or (H₁ : a ∨ b) (H₂ : a → c) (H₃ : b → d) : c ∨ d :=
  elim H₁
    (assume Ha : a, inl (H₂ Ha))
    (assume Hb : b, inr (H₃ Hb))

  theorem imp_or_left (H₁ : a ∨ c) (H : a → b) : b ∨ c :=
  elim H₁
    (assume H₂ : a, inl (H H₂))
    (assume H₂ : c, inr H₂)

  theorem imp_or_right (H₁ : c ∨ a) (H : a → b) : c ∨ b :=
  elim H₁
    (assume H₂ : c, inl H₂)
    (assume H₂ : a, inr (H H₂))
end or

theorem not_not_em {p : Prop} : ¬¬(p ∨ ¬p) :=
assume not_em : ¬(p ∨ ¬p),
  have Hnp : ¬p, from
    assume Hp : p, absurd (or.inl Hp) not_em,
  absurd (or.inr Hnp) not_em

-- iff
-- ---
definition iff (a b : Prop) := (a → b) ∧ (b → a)

notation a <-> b := iff a b
notation a ↔ b := iff a b

namespace iff
  definition def : (a ↔ b) = ((a → b) ∧ (b → a)) :=
  rfl

  definition intro (H₁ : a → b) (H₂ : b → a) : a ↔ b :=
  and.intro H₁ H₂

  definition elim (H₁ : (a → b) → (b → a) → c) (H₂ : a ↔ b) : c :=
  and.rec H₁ H₂

  definition elim_left (H : a ↔ b) : a → b :=
  elim (assume H₁ H₂, H₁) H

  definition mp := @elim_left

  definition elim_right (H : a ↔ b) : b → a :=
  elim (assume H₁ H₂, H₂) H

  definition flip_sign (H₁ : a ↔ b) : ¬a ↔ ¬b :=
  intro
    (assume Hna, mt (elim_right H₁) Hna)
    (assume Hnb, mt (elim_left H₁) Hnb)

  definition refl (a : Prop) : a ↔ a :=
  intro (assume H, H) (assume H, H)

  definition rfl {a : Prop} : a ↔ a :=
  refl a

  theorem trans (H₁ : a ↔ b) (H₂ : b ↔ c) : a ↔ c :=
  intro
    (assume Ha, elim_left H₂ (elim_left H₁ Ha))
    (assume Hc, elim_right H₁ (elim_right H₂ Hc))

  theorem symm (H : a ↔ b) : b ↔ a :=
  intro
    (assume Hb, elim_right H Hb)
    (assume Ha, elim_left H Ha)

  theorem true_elim (H : a ↔ true) : a :=
  mp (symm H) trivial

  theorem false_elim (H : a ↔ false) : ¬a :=
  assume Ha : a, mp H Ha
end iff

calc_refl iff.refl
calc_trans iff.trans

open eq.ops

theorem eq_to_iff {a b : Prop} (H : a = b) : a ↔ b :=
iff.intro (λ Ha, H ▸ Ha) (λ Hb, H⁻¹ ▸ Hb)

-- comm and assoc for and / or
-- ---------------------------
namespace and
  theorem comm : a ∧ b ↔ b ∧ a :=
  iff.intro (λH, swap H) (λH, swap H)

  theorem assoc : (a ∧ b) ∧ c ↔ a ∧ (b ∧ c) :=
  iff.intro
    (assume H, intro
      (elim_left (elim_left H))
      (intro (elim_right (elim_left H)) (elim_right H)))
    (assume H, intro
      (intro (elim_left H) (elim_left (elim_right H)))
      (elim_right (elim_right H)))
end and

namespace or
  theorem comm : a ∨ b ↔ b ∨ a :=
  iff.intro (λH, swap H) (λH, swap H)

  theorem assoc : (a ∨ b) ∨ c ↔ a ∨ (b ∨ c) :=
  iff.intro
    (assume H, elim H
      (assume H₁, elim H₁
        (assume Ha, inl Ha)
        (assume Hb, inr (inl Hb)))
      (assume Hc, inr (inr Hc)))
    (assume H, elim H
      (assume Ha, (inl (inl Ha)))
      (assume H₁, elim H₁
        (assume Hb, inl (inr Hb))
        (assume Hc, inr Hc)))
end or
