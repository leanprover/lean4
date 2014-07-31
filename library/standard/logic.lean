-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Leonardo de Moura, Jeremy Avigad

definition Prop [inline] := Type.{0}

abbreviation imp (a b : Prop) : Prop := a → b


-- true and false
-- --------------

inductive false : Prop

theorem false_elim (c : Prop) (H : false) : c :=
false_rec c H

inductive true : Prop :=
| trivial : true

abbreviation not (a : Prop) := a → false
prefix `¬`:40 := not

notation `assume` binders `,` r:(scoped f, f) := r
notation `take`   binders `,` r:(scoped f, f) := r


-- not
-- ---

theorem not_intro {a : Prop} (H : a → false) : ¬a := H

theorem not_elim {a : Prop} (H1 : ¬a) (H2 : a) : false := H1 H2

theorem absurd {a : Prop} (H1 : a) (H2 : ¬a) : false := H2 H1

theorem not_not_intro {a : Prop} (Ha : a) : ¬¬a :=
assume Hna : ¬a, absurd Ha Hna

theorem mt {a b : Prop} (H1 : a → b) (H2 : ¬b) : ¬a :=
assume Ha : a, absurd (H1 Ha) H2

theorem contrapos {a b : Prop} (H : a → b) : ¬b → ¬a :=
assume Hnb : ¬b, mt H Hnb

theorem absurd_elim {a : Prop} (b : Prop) (H1 : a) (H2 : ¬a) : b :=
false_elim b (absurd H1 H2)

theorem absurd_not_true (H : ¬true) : false :=
absurd trivial H

theorem not_false_trivial : ¬false :=
assume H : false, H

theorem not_implies_left {a b : Prop} (H : ¬(a → b)) : ¬¬a :=
assume Hna : ¬a, absurd (assume Ha : a, absurd_elim b Ha Hna) H

theorem not_implies_right {a b : Prop} (H : ¬(a → b)) : ¬b :=
assume Hb : b, absurd (assume Ha : a, Hb) H


-- and
-- ---

inductive and (a b : Prop) : Prop :=
| and_intro : a → b → and a b

infixr `/\`:35 := and
infixr `∧`:35 := and

theorem and_elim {a b c : Prop} (H1 : a ∧ b) (H2 : a → b → c) : c :=
and_rec H2 H1

theorem and_elim_left {a b : Prop} (H : a ∧ b) : a  :=
and_rec (λa b, a) H

theorem and_elim_right {a b : Prop} (H : a ∧ b) : b :=
and_rec (λa b, b) H

theorem and_swap {a b : Prop} (H : a ∧ b) : b ∧ a :=
and_intro (and_elim_right H) (and_elim_left H)

theorem and_not_left {a : Prop} (b : Prop) (Hna : ¬a) : ¬(a ∧ b) :=
assume H : a ∧ b, absurd (and_elim_left H) Hna

theorem and_not_right (a : Prop) {b : Prop} (Hnb : ¬b) : ¬(a ∧ b) :=
assume H : a ∧ b, absurd (and_elim_right H) Hnb

theorem and_imp_and {a b c d : Prop} (H1 : a ∧ b) (H2 : a → c) (H3 : b → d) : c ∧ d :=
and_elim H1 (assume Ha : a, assume Hb : b, and_intro (H2 Ha) (H3 Hb))

theorem imp_and_left {a b c : Prop} (H1 : a ∧ c) (H : a → b) : b ∧ c :=
and_elim H1 (assume Ha : a, assume Hc : c, and_intro (H Ha) Hc)

theorem imp_and_right {a b c : Prop} (H1 : c ∧ a) (H : a → b) : c ∧ b :=
and_elim H1 (assume Hc : c, assume Ha : a, and_intro Hc (H Ha))


-- or
-- --

inductive or (a b : Prop) : Prop :=
| or_intro_left  : a → or a b
| or_intro_right : b → or a b

infixr `\/`:30 := or
infixr `∨`:30 := or

theorem or_inl {a b : Prop} (Ha : a) : a ∨ b := or_intro_left b Ha
theorem or_inr {a b : Prop} (Hb : b) : a ∨ b := or_intro_right a Hb

theorem or_elim {a b c : Prop} (H1 : a ∨ b) (H2 : a → c) (H3 : b → c) : c :=
or_rec H2 H3 H1

theorem resolve_right {a b : Prop} (H1 : a ∨ b) (H2 : ¬a) : b :=
or_elim H1 (assume Ha, absurd_elim b Ha H2) (assume Hb, Hb)

theorem resolve_left {a b : Prop} (H1 : a ∨ b) (H2 : ¬b) : a :=
or_elim H1 (assume Ha, Ha) (assume Hb, absurd_elim a Hb H2)

theorem or_swap {a b : Prop} (H : a ∨ b) : b ∨ a :=
or_elim H (assume Ha, or_inr Ha) (assume Hb, or_inl Hb)

theorem or_not_intro {a b : Prop} (Hna : ¬a) (Hnb : ¬b) : ¬(a ∨ b) :=
assume H : a ∨ b, or_elim H
  (assume Ha, absurd_elim _ Ha Hna)
  (assume Hb, absurd_elim _ Hb Hnb)

theorem or_imp_or {a b c d : Prop} (H1 : a ∨ b) (H2 : a → c) (H3 : b → d) : c ∨ d :=
or_elim H1
  (assume Ha : a, or_inl (H2 Ha))
  (assume Hb : b, or_inr (H3 Hb))

theorem imp_or_left {a b c : Prop} (H1 : a ∨ c) (H : a → b) : b ∨ c :=
or_elim H1
  (assume H2 : a, or_inl (H H2))
  (assume H2 : c, or_inr H2)

theorem imp_or_right {a b c : Prop} (H1 : c ∨ a) (H : a → b) : c ∨ b :=
or_elim H1
  (assume H2 : c, or_inl H2)
  (assume H2 : a, or_inr (H H2))


-- eq
-- --

inductive eq {A : Type} (a : A) : A → Prop :=
| refl : eq a a

infix `=`:50 := eq

theorem subst {A : Type} {a b : A} {P : A → Prop} (H1 : a = b) (H2 : P a) : P b :=
eq_rec H2 H1

theorem trans {A : Type} {a b c : A} (H1 : a = b) (H2 : b = c) : a = c :=
subst H2 H1

calc_subst subst
calc_refl  refl
calc_trans trans

theorem true_ne_false : ¬true = false :=
assume H : true = false,
  subst H trivial

theorem symm {A : Type} {a b : A} (H : a = b) : b = a :=
subst H (refl a)

namespace eq_proofs
  postfix `⁻¹`:100 := symm
  infixr `⬝`:75     := trans
  infixr `▸`:75    := subst
end
using eq_proofs

theorem congr1 {A : Type} {B : A → Type} {f g : Π x, B x} (H : f = g) (a : A) : f a = g a :=
H ▸ refl (f a)

theorem congr2 {A : Type} {B : Type} {a b : A} (f : A → B) (H : a = b) : f a = f b :=
H ▸ refl (f a)

theorem congr {A : Type} {B : Type} {f g : A → B} {a b : A} (H1 : f = g) (H2 : a = b) : f a = g b :=
H1 ▸ H2 ▸ refl (f a)

theorem equal_f {A : Type} {B : A → Type} {f g : Π x, B x} (H : f = g) : ∀x, f x = g x :=
take x, congr1 H x

theorem not_congr {a b : Prop} (H : a = b) : (¬a) = (¬b) :=
congr2 not H

theorem eqmp {a b : Prop} (H1 : a = b) (H2 : a) : b :=
H1 ▸ H2

infixl `<|`:100 := eqmp
infixl `◂`:100 := eqmp

theorem eqmpr {a b : Prop} (H1 : a = b) (H2 : b) : a :=
H1⁻¹ ◂ H2

theorem eqt_elim {a : Prop} (H : a = true) : a :=
H⁻¹ ◂ trivial

theorem eqf_elim {a : Prop} (H : a = false) : ¬a :=
assume Ha : a, H ◂ Ha

theorem imp_trans {a b c : Prop} (H1 : a → b) (H2 : b → c) : a → c :=
assume Ha, H2 (H1 Ha)

theorem imp_eq_trans {a b c : Prop} (H1 : a → b) (H2 : b = c) : a → c :=
assume Ha, H2 ◂ (H1 Ha)

theorem eq_imp_trans {a b c : Prop} (H1 : a = b) (H2 : b → c) : a → c :=
assume Ha, H2 (H1 ◂ Ha)


-- ne
-- --

definition ne [inline] {A : Type} (a b : A) := ¬(a = b)
infix `≠`:50 := ne

theorem ne_intro {A : Type} {a b : A} (H : a = b → false) : a ≠ b := H

theorem ne_elim {A : Type} {a b : A} (H1 : a ≠ b) (H2 : a = b) : false := H1 H2

theorem a_neq_a_elim {A : Type} {a : A} (H : a ≠ a) : false := H (refl a)

theorem ne_irrefl {A : Type} {a : A} (H : a ≠ a) : false := H (refl a)

theorem ne_symm {A : Type} {a b : A} (H : a ≠ b) : b ≠ a :=
assume H1 : b = a, H (H1⁻¹)

theorem eq_ne_trans {A : Type} {a b c : A} (H1 : a = b) (H2 : b ≠ c) : a ≠ c := H1⁻¹ ▸ H2

theorem ne_eq_trans {A : Type} {a b c : A} (H1 : a ≠ b) (H2 : b = c) : a ≠ c := H2 ▸ H1

calc_trans eq_ne_trans
calc_trans ne_eq_trans


-- iff
-- ---

definition iff (a b : Prop) := (a → b) ∧ (b → a)
infix `<->`:25 := iff
infix `↔`:25 := iff

theorem iff_intro {a b : Prop} (H1 : a → b) (H2 : b → a) : a ↔ b := and_intro H1 H2

theorem iff_elim {a b c : Prop} (H1 : (a → b) → (b → a) → c) (H2 : a ↔ b) : c := and_rec H1 H2

theorem iff_elim_left {a b : Prop} (H : a ↔ b) : a → b :=
iff_elim (assume H1 H2, H1) H

theorem iff_elim_right {a b : Prop} (H : a ↔ b) : b → a :=
iff_elim (assume H1 H2, H2) H

theorem iff_flip_sign {a b : Prop} (H1 : a ↔ b) : ¬a ↔ ¬b :=
iff_intro
  (assume Hna, mt (iff_elim_right H1) Hna)
  (assume Hnb, mt (iff_elim_left H1) Hnb)

theorem iff_refl (a : Prop) : a ↔ a :=
iff_intro (assume H, H) (assume H, H)

theorem iff_trans {a b c : Prop} (H1 : a ↔ b) (H2 : b ↔ c) : a ↔ c :=
iff_intro
  (assume Ha, iff_elim_left H2 (iff_elim_left H1 Ha))
  (assume Hc, iff_elim_right H1 (iff_elim_right H2 Hc))

theorem iff_symm {a b : Prop} (H : a ↔ b) : b ↔ a :=
iff_intro
  (assume Hb, iff_elim_right H Hb)
  (assume Ha, iff_elim_left H Ha)

calc_trans iff_trans

theorem eq_to_iff {a b : Prop} (H : a = b) : a ↔ b :=
iff_intro (λ Ha, H ▸ Ha) (λ Hb, H⁻¹ ▸ Hb)


-- comm and assoc for and / or
-- ---------------------------

theorem and_comm (a b : Prop) : a ∧ b ↔ b ∧ a :=
iff_intro (λH, and_swap H) (λH, and_swap H)

theorem and_assoc (a b c : Prop) : (a ∧ b) ∧ c ↔ a ∧ (b ∧ c) :=
iff_intro
  (assume H, and_intro
    (and_elim_left (and_elim_left H))
    (and_intro (and_elim_right (and_elim_left H)) (and_elim_right H)))
  (assume H, and_intro
    (and_intro (and_elim_left H) (and_elim_left (and_elim_right H)))
    (and_elim_right (and_elim_right H)))

theorem or_comm (a b : Prop) : a ∨ b ↔ b ∨ a :=
iff_intro (λH, or_swap H) (λH, or_swap H)

theorem or_assoc (a b c : Prop) : (a ∨ b) ∨ c ↔ a ∨ (b ∨ c) :=
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


-- exists
-- ------

inductive Exists {A : Type} (P : A → Prop) : Prop :=
| exists_intro : ∀ (a : A), P a → Exists P

notation `exists` binders `,` r:(scoped P, Exists P) := r
notation `∃` binders `,` r:(scoped P, Exists P) := r

theorem exists_elim {A : Type} {p : A → Prop} {B : Prop} (H1 : ∃x, p x) (H2 : ∀ (a : A) (H : p a), B) : B :=
Exists_rec H2 H1

theorem exists_not_forall {A : Type} {p : A → Prop} (H : ∃x, p x) : ¬∀x, ¬p x :=
assume H1 : ∀x, ¬p x,
  obtain (w : A) (Hw : p w), from H,
  absurd Hw (H1 w)

theorem forall_not_exists {A : Type} {p : A → Prop} (H2 : ∀x, p x) : ¬∃x, ¬p x :=
assume H1 : ∃x, ¬p x,
  obtain (w : A) (Hw : ¬p w), from H1,
  absurd (H2 w) Hw

definition exists_unique {A : Type} (p : A → Prop) :=
∃x, p x ∧ ∀y, y ≠ x → ¬p y

notation `∃!` binders `,` r:(scoped P, exists_unique P) := r

theorem exists_unique_intro {A : Type} {p : A → Prop} (w : A) (H1 : p w) (H2 : ∀y, y ≠ w → ¬p y) : ∃!x, p x :=
exists_intro w (and_intro H1 H2)

theorem exists_unique_elim {A : Type} {p : A → Prop} {b : Prop}
                           (H2 : ∃!x, p x) (H1 : ∀x, p x → (∀y, y ≠ x → ¬p y) → b) : b :=
obtain w Hw, from H2,
H1 w (and_elim_left Hw) (and_elim_right Hw)


-- inhabited
-- ---------

inductive inhabited (A : Type) : Prop :=
| inhabited_intro : A → inhabited A

theorem inhabited_elim {A : Type} {B : Prop} (H1 : inhabited A) (H2 : A → B) : B :=
inhabited_rec H2 H1

theorem inhabited_Prop [instance] : inhabited Prop :=
inhabited_intro true

theorem inhabited_fun [instance] (A : Type) {B : Type} (H : inhabited B) : inhabited (A → B) :=
inhabited_elim H (take b, inhabited_intro (λa, b))

theorem inhabited_exists {A : Type} {p : A → Prop} (H : ∃x, p x) : inhabited A :=
obtain w Hw, from H, inhabited_intro w
