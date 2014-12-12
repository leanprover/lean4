-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Jeremy Avigad, Leonardo de Moura

definition imp (a b : Prop) : Prop := a → b

variables {a b c d : Prop}

theorem mt (H1 : a → b) (H2 : ¬b) : ¬a :=
assume Ha : a, absurd (H1 Ha) H2

-- make c explicit and rename to false.elim
theorem false_elim {c : Prop} (H : false) : c :=
false.rec c H

-- not
-- ---

theorem not_elim (H1 : ¬a) (H2 : a) : false := H1 H2

theorem not_intro (H : a → false) : ¬a := H

theorem not_not_intro (Ha : a) : ¬¬a :=
assume Hna : ¬a, absurd Ha Hna

theorem not_implies_left (H : ¬(a → b)) : ¬¬a :=
assume Hna : ¬a, absurd (assume Ha : a, absurd Ha Hna) H

theorem not_implies_right (H : ¬(a → b)) : ¬b :=
assume Hb : b, absurd (assume Ha : a, Hb) H

theorem not_not_em : ¬¬(a ∨ ¬a) :=
assume not_em : ¬(a ∨ ¬a),
  have Hnp : ¬a, from
    assume Hp : a, absurd (or.inl Hp) not_em,
  absurd (or.inr Hnp) not_em

-- and
-- ---

namespace and
  theorem swap (H : a ∧ b) : b ∧ a :=
  intro (elim_right H) (elim_left H)

  theorem imp_and (H₁ : a ∧ b) (H₂ : a → c) (H₃ : b → d) : c ∧ d :=
  elim H₁ (assume Ha : a, assume Hb : b, intro (H₂ Ha) (H₃ Hb))

  theorem imp_left (H₁ : a ∧ c) (H : a → b) : b ∧ c :=
  elim H₁ (assume Ha : a, assume Hc : c, intro (H Ha) Hc)

  theorem imp_right (H₁ : c ∧ a) (H : a → b) : c ∧ b :=
  elim H₁ (assume Hc : c, assume Ha : a, intro Hc (H Ha))

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

-- or
-- --

namespace or
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

  theorem elim3 (H : a ∨ b ∨ c) (Ha : a → d) (Hb : b → d) (Hc : c → d) : d :=
  elim H Ha (assume H₂, elim H₂ Hb Hc)

  theorem resolve_right (H₁ : a ∨ b) (H₂ : ¬a) : b :=
  elim H₁ (assume Ha, absurd Ha H₂) (assume Hb, Hb)

  theorem resolve_left (H₁ : a ∨ b) (H₂ : ¬b) : a :=
  elim H₁ (assume Ha, Ha) (assume Hb, absurd Hb H₂)

  theorem swap (H : a ∨ b) : b ∨ a :=
  elim H (assume Ha, inr Ha) (assume Hb, inl Hb)

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

-- iff
-- ---

namespace iff
  definition def : (a ↔ b) = ((a → b) ∧ (b → a)) :=
  !eq.refl

end iff

-- exists_unique
-- -------------

definition exists_unique {A : Type} (p : A → Prop) :=
∃x, p x ∧ ∀y, p y → y = x

notation `∃!` binders `,` r:(scoped P, exists_unique P) := r

theorem exists_unique_intro {A : Type} {p : A → Prop} (w : A) (H1 : p w) (H2 : ∀y, p y → y = w) : ∃!x, p x :=
exists_intro w (and.intro H1 H2)

theorem exists_unique_elim {A : Type} {p : A → Prop} {b : Prop}
                           (H2 : ∃!x, p x) (H1 : ∀x, p x → (∀y, p y → y = x) → b) : b :=
obtain w Hw, from H2,
H1 w (and.elim_left Hw) (and.elim_right Hw)
