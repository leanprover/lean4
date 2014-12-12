/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
-/
prelude
import init.datatypes init.reserved_notation

-- implication
-- -----------

definition imp (a b : Prop) : Prop := a → b

-- make c explicit and rename to false.elim
theorem false_elim {c : Prop} (H : false) : c :=
false.rec c H

definition trivial := true.intro

definition not (a : Prop) := a → false
prefix `¬` := not

definition absurd {a : Prop} {b : Type} (H1 : a) (H2 : ¬a) : b :=
false.rec b (H2 H1)

theorem mt {a b : Prop} (H1 : a → b) (H2 : ¬b) : ¬a :=
assume Ha : a, absurd (H1 Ha) H2

-- not
-- ---

theorem not_false : ¬false :=
assume H : false, H

theorem not_not_intro {a : Prop} (Ha : a) : ¬¬a :=
assume Hna : ¬a, absurd Ha Hna

theorem not_intro {a : Prop} (H : a → false) : ¬a := H

theorem not_elim {a : Prop} (H1 : ¬a) (H2 : a) : false := H1 H2

theorem not_implies_left {a b : Prop} (H : ¬(a → b)) : ¬¬a :=
assume Hna : ¬a, absurd (assume Ha : a, absurd Ha Hna) H

theorem not_implies_right {a b : Prop} (H : ¬(a → b)) : ¬b :=
assume Hb : b, absurd (assume Ha : a, Hb) H

-- eq
-- --

notation a = b := eq a b
definition rfl {A : Type} {a : A} := eq.refl a

-- proof irrelevance is built in
theorem proof_irrel {a : Prop} (H₁ H₂ : a) : H₁ = H₂ :=
rfl

namespace eq
  variables {A : Type}
  variables {a b c a': A}

  definition drec_on {B : Πa' : A, a = a' → Type} (H₁ : a = a') (H₂ : B a (refl a)) : B a' H₁ :=
  eq.rec (λH₁ : a = a, show B a H₁, from H₂) H₁ H₁

  theorem id_refl (H₁ : a = a) : H₁ = (eq.refl a) :=
  rfl

  theorem irrel (H₁ H₂ : a = b) : H₁ = H₂ :=
  !proof_irrel

  theorem subst {P : A → Prop} (H₁ : a = b) (H₂ : P a) : P b :=
  rec H₂ H₁

  theorem trans (H₁ : a = b) (H₂ : b = c) : a = c :=
  subst H₂ H₁

  definition symm (H : a = b) : b = a :=
  subst H (refl a)

  namespace ops
    notation H `⁻¹` := symm H --input with \sy or \-1 or \inv
    notation H1 ⬝ H2 := trans H1 H2
    notation H1 ▸ H2 := subst H1 H2
  end ops

  variable {p : Prop}
  open ops

  theorem true_elim (H : p = true) : p :=
  H⁻¹ ▸ trivial

  theorem false_elim (H : p = false) : ¬p :=
  assume Hp, H ▸ Hp
end eq

calc_subst eq.subst
calc_refl  eq.refl
calc_trans eq.trans
calc_symm  eq.symm

-- ne
-- --

definition ne {A : Type} (a b : A) := ¬(a = b)
notation a ≠ b := ne a b

namespace ne
  open eq.ops
  variable {A : Type}
  variables {a b : A}

  theorem intro : (a = b → false) → a ≠ b :=
  assume H, H

  theorem elim : a ≠ b → a = b → false :=
  assume H₁ H₂, H₁ H₂

  theorem irrefl : a ≠ a → false :=
  assume H, H rfl

  theorem symm : a ≠ b → b ≠ a :=
  assume (H : a ≠ b) (H₁ : b = a), H (H₁⁻¹)
end ne

section
  open eq.ops
  variables {A : Type} {a b c : A}

  theorem false.of_ne : a ≠ a → false :=
  assume H, H rfl

  theorem ne.of_eq_of_ne : a = b → b ≠ c → a ≠ c :=
  assume H₁ H₂, H₁⁻¹ ▸ H₂

  theorem ne.of_ne_of_eq : a ≠ b → b = c → a ≠ c :=
  assume H₁ H₂, H₂ ▸ H₁
end

calc_trans ne.of_eq_of_ne
calc_trans ne.of_ne_of_eq

infixl `==`:50 := heq

namespace heq
  universe variable u
  variables {A B C : Type.{u}} {a a' : A} {b b' : B} {c : C}

  definition to_eq (H : a == a') : a = a' :=
  have H₁ : ∀ (Ht : A = A), eq.rec_on Ht a = a, from
    λ Ht, eq.refl (eq.rec_on Ht a),
  heq.rec_on H H₁ (eq.refl A)

  definition elim {A : Type} {a : A} {P : A → Type} {b : A} (H₁ : a == b) (H₂ : P a) : P b :=
  eq.rec_on (to_eq H₁) H₂

  theorem drec_on {C : Π {B : Type} (b : B), a == b → Type} (H₁ : a == b) (H₂ : C a (refl a)) : C b H₁ :=
  rec (λ H₁ : a == a, show C a H₁, from H₂) H₁ H₁

  theorem subst {P : ∀T : Type, T → Prop} (H₁ : a == b) (H₂ : P A a) : P B b :=
  rec_on H₁ H₂

  theorem symm (H : a == b) : b == a :=
  rec_on H (refl a)

  definition type_eq (H : a == b) : A = B :=
  heq.rec_on H (eq.refl A)

  theorem from_eq (H : a = a') : a == a' :=
  eq.subst H (refl a)

  theorem trans (H₁ : a == b) (H₂ : b == c) : a == c :=
  subst H₂ H₁

  theorem trans_left (H₁ : a == b) (H₂ : b = b') : a == b' :=
  trans H₁ (from_eq H₂)

  theorem trans_right (H₁ : a = a') (H₂ : a' == b) : a == b :=
  trans (from_eq H₁) H₂

  theorem true_elim {a : Prop} (H : a == true) : a :=
  eq.true_elim (heq.to_eq H)
end heq

calc_trans heq.trans
calc_trans heq.trans_left
calc_trans heq.trans_right
calc_symm  heq.symm

-- and
-- ---

notation a /\ b := and a b
notation a ∧ b  := and a b

variables {a b c d : Prop}

namespace and
  theorem elim (H₁ : a ∧ b) (H₂ : a → b → c) : c :=
  rec H₂ H₁

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

  open eq.ops
  theorem of_eq {a b : Prop} (H : a = b) : a ↔ b :=
  iff.intro (λ Ha, H ▸ Ha) (λ Hb, H⁻¹ ▸ Hb)
end iff

calc_refl iff.refl
calc_trans iff.trans

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

inductive Exists {A : Type} (P : A → Prop) : Prop :=
intro : ∀ (a : A), P a → Exists P

definition exists_intro := @Exists.intro

notation `exists` binders `,` r:(scoped P, Exists P) := r
notation `∃` binders `,` r:(scoped P, Exists P) := r

theorem exists_elim {A : Type} {p : A → Prop} {B : Prop} (H1 : ∃x, p x) (H2 : ∀ (a : A) (H : p a), B) : B :=
Exists.rec H2 H1

definition exists_unique {A : Type} (p : A → Prop) :=
∃x, p x ∧ ∀y, p y → y = x

notation `∃!` binders `,` r:(scoped P, exists_unique P) := r

theorem exists_unique_intro {A : Type} {p : A → Prop} (w : A) (H1 : p w) (H2 : ∀y, p y → y = w) : ∃!x, p x :=
exists_intro w (and.intro H1 H2)

theorem exists_unique_elim {A : Type} {p : A → Prop} {b : Prop}
                           (H2 : ∃!x, p x) (H1 : ∀x, p x → (∀y, p y → y = x) → b) : b :=
obtain w Hw, from H2,
H1 w (and.elim_left Hw) (and.elim_right Hw)

inductive decidable [class] (p : Prop) : Type :=
inl :  p → decidable p,
inr : ¬p → decidable p


definition true.decidable [instance] : decidable true :=
decidable.inl trivial

definition false.decidable [instance] : decidable false :=
decidable.inr not_false

namespace decidable
  variables {p q : Prop}

  definition rec_on_true [H : decidable p] {H1 : p → Type} {H2 : ¬p → Type} (H3 : p) (H4 : H1 H3)
      : rec_on H H1 H2 :=
  rec_on H (λh, H4) (λh, false.rec _ (h H3))

  definition rec_on_false [H : decidable p] {H1 : p → Type} {H2 : ¬p → Type} (H3 : ¬p) (H4 : H2 H3)
      : rec_on H H1 H2 :=
  rec_on H (λh, false.rec _ (H3 h)) (λh, H4)

  definition by_cases {q : Type} [C : decidable p] (Hpq : p → q) (Hnpq : ¬p → q) : q :=
  rec_on C (assume Hp, Hpq Hp) (assume Hnp, Hnpq Hnp)

  theorem em (p : Prop) [H : decidable p] : p ∨ ¬p :=
  by_cases (λ Hp, or.inl Hp) (λ Hnp, or.inr Hnp)

  theorem by_contradiction [Hp : decidable p] (H : ¬p → false) : p :=
  by_cases
    (assume H1 : p, H1)
    (assume H1 : ¬p, false_elim (H H1))

  definition decidable_iff_equiv (Hp : decidable p) (H : p ↔ q) : decidable q :=
  rec_on Hp
    (assume Hp : p,   inl (iff.elim_left H Hp))
    (assume Hnp : ¬p, inr (iff.elim_left (iff.flip_sign H) Hnp))

  definition decidable_eq_equiv (Hp : decidable p) (H : p = q) : decidable q :=
  decidable_iff_equiv Hp (iff.of_eq H)
end decidable

section
  variables {p q : Prop}
  open decidable (rec_on inl inr)

  definition and.decidable [instance] (Hp : decidable p) (Hq : decidable q) : decidable (p ∧ q) :=
  rec_on Hp
    (assume Hp  : p, rec_on Hq
      (assume Hq  : q,  inl (and.intro Hp Hq))
      (assume Hnq : ¬q, inr (and.not_right p Hnq)))
    (assume Hnp : ¬p, inr (and.not_left q Hnp))

  definition or.decidable [instance] (Hp : decidable p) (Hq : decidable q) : decidable (p ∨ q) :=
  rec_on Hp
    (assume Hp  : p, inl (or.inl Hp))
    (assume Hnp : ¬p, rec_on Hq
      (assume Hq  : q,  inl (or.inr Hq))
      (assume Hnq : ¬q, inr (or.not_intro Hnp Hnq)))

  definition not.decidable [instance] (Hp : decidable p) : decidable (¬p) :=
  rec_on Hp
    (assume Hp,  inr (not_not_intro Hp))
    (assume Hnp, inl Hnp)

  definition implies.decidable [instance] (Hp : decidable p) (Hq : decidable q) : decidable (p → q) :=
  rec_on Hp
    (assume Hp  : p, rec_on Hq
      (assume Hq  : q,  inl (assume H, Hq))
      (assume Hnq : ¬q, inr (assume H : p → q, absurd (H Hp) Hnq)))
    (assume Hnp : ¬p, inl (assume Hp, absurd Hp Hnp))

  definition iff.decidable [instance] (Hp : decidable p) (Hq : decidable q) : decidable (p ↔ q) := _
end

definition decidable_pred {A : Type} (R : A   →   Prop) := Π (a   : A), decidable (R a)
definition decidable_rel  {A : Type} (R : A → A → Prop) := Π (a b : A), decidable (R a b)
definition decidable_eq   (A : Type) := decidable_rel (@eq A)

inductive inhabited [class] (A : Type) : Type :=
mk : A → inhabited A

namespace inhabited

protected definition destruct {A : Type} {B : Type} (H1 : inhabited A) (H2 : A → B) : B :=
inhabited.rec H2 H1

definition Prop_inhabited [instance] : inhabited Prop :=
mk true

definition fun_inhabited [instance] (A : Type) {B : Type} (H : inhabited B) : inhabited (A → B) :=
destruct H (λb, mk (λa, b))

definition dfun_inhabited [instance] (A : Type) {B : A → Type} (H : Πx, inhabited (B x)) :
  inhabited (Πx, B x) :=
mk (λa, destruct (H a) (λb, b))

definition default (A : Type) [H : inhabited A] : A := destruct H (take a, a)

end inhabited

inductive nonempty [class] (A : Type) : Prop :=
intro : A → nonempty A

namespace nonempty
  protected definition elim {A : Type} {B : Prop} (H1 : nonempty A) (H2 : A → B) : B :=
  rec H2 H1

  theorem inhabited_imp_nonempty [instance] {A : Type} (H : inhabited A) : nonempty A :=
  intro (inhabited.default A)
end nonempty

definition ite (c : Prop) [H : decidable c] {A : Type} (t e : A) : A :=
decidable.rec_on H (λ Hc, t) (λ Hnc, e)

definition if_pos {c : Prop} [H : decidable c] (Hc : c) {A : Type} {t e : A} : (if c then t else e) = t :=
decidable.rec
  (λ Hc : c,    eq.refl (@ite c (decidable.inl Hc) A t e))
  (λ Hnc : ¬c,  absurd Hc Hnc)
  H

definition if_neg {c : Prop} [H : decidable c] (Hnc : ¬c) {A : Type} {t e : A} : (if c then t else e) = e :=
decidable.rec
  (λ Hc : c,    absurd Hc Hnc)
  (λ Hnc : ¬c,  eq.refl (@ite c (decidable.inr Hnc) A t e))
  H

definition if_t_t (c : Prop) [H : decidable c] {A : Type} (t : A) : (if c then t else t) = t :=
decidable.rec
  (λ Hc  : c,  eq.refl (@ite c (decidable.inl Hc)  A t t))
  (λ Hnc : ¬c, eq.refl (@ite c (decidable.inr Hnc) A t t))
  H

definition if_true {A : Type} (t e : A) : (if true then t else e) = t :=
if_pos trivial

definition if_false {A : Type} (t e : A) : (if false then t else e) = e :=
if_neg not_false

theorem if_cond_congr {c₁ c₂ : Prop} [H₁ : decidable c₁] [H₂ : decidable c₂] (Heq : c₁ ↔ c₂) {A : Type} (t e : A)
                      : (if c₁ then t else e) = (if c₂ then t else e) :=
decidable.rec_on H₁
 (λ Hc₁  : c₁,  decidable.rec_on H₂
   (λ Hc₂  : c₂,  if_pos Hc₁ ⬝ (if_pos Hc₂)⁻¹)
   (λ Hnc₂ : ¬c₂, absurd (iff.elim_left Heq Hc₁) Hnc₂))
 (λ Hnc₁ : ¬c₁, decidable.rec_on H₂
   (λ Hc₂  : c₂,  absurd (iff.elim_right Heq Hc₂) Hnc₁)
   (λ Hnc₂ : ¬c₂, if_neg Hnc₁ ⬝ (if_neg Hnc₂)⁻¹))

theorem if_congr_aux {c₁ c₂ : Prop} [H₁ : decidable c₁] [H₂ : decidable c₂] {A : Type} {t₁ t₂ e₁ e₂ : A}
                     (Hc : c₁ ↔ c₂) (Ht : t₁ = t₂) (He : e₁ = e₂) :
                 (if c₁ then t₁ else e₁) = (if c₂ then t₂ else e₂) :=
Ht ▸ He ▸ (if_cond_congr Hc t₁ e₁)

theorem if_congr {c₁ c₂ : Prop} [H₁ : decidable c₁] {A : Type} {t₁ t₂ e₁ e₂ : A} (Hc : c₁ ↔ c₂) (Ht : t₁ = t₂) (He : e₁ = e₂) :
                 (if c₁ then t₁ else e₁) = (@ite c₂ (decidable.decidable_iff_equiv H₁ Hc) A t₂ e₂) :=
have H2 [visible] : decidable c₂, from (decidable.decidable_iff_equiv H₁ Hc),
if_congr_aux Hc Ht He

-- We use "dependent" if-then-else to be able to communicate the if-then-else condition
-- to the branches
definition dite (c : Prop) [H : decidable c] {A : Type} (t : c → A) (e : ¬ c → A) : A :=
decidable.rec_on H (λ Hc, t Hc) (λ Hnc, e Hnc)

definition dif_pos {c : Prop} [H : decidable c] (Hc : c) {A : Type} {t : c → A} {e : ¬ c → A} : (if H : c then t H else e H) = t Hc :=
decidable.rec
  (λ Hc : c,    eq.refl (@dite c (decidable.inl Hc) A t e))
  (λ Hnc : ¬c,  absurd Hc Hnc)
  H

definition dif_neg {c : Prop} [H : decidable c] (Hnc : ¬c) {A : Type} {t : c → A} {e : ¬ c → A} : (if H : c then t H else e H) = e Hnc :=
decidable.rec
  (λ Hc : c,    absurd Hc Hnc)
  (λ Hnc : ¬c,  eq.refl (@dite c (decidable.inr Hnc) A t e))
  H

-- Remark: dite and ite are "definitionally equal" when we ignore the proofs.
theorem dite_ite_eq (c : Prop) [H : decidable c] {A : Type} (t : A) (e : A) : dite c (λh, t) (λh, e) = ite c t e :=
rfl

definition is_true (c : Prop) [H : decidable c] : Prop :=
if c then true else false

definition is_false (c : Prop) [H : decidable c] : Prop :=
if c then false else true

theorem of_is_true {c : Prop} [H₁ : decidable c] (H₂ : is_true c) : c :=
decidable.rec_on H₁ (λ Hc, Hc) (λ Hnc, false_elim (if_neg Hnc ▸ H₂))

theorem not_of_not_is_true {c : Prop} [H₁ : decidable c] (H₂ : ¬ is_true c) : ¬ c :=
decidable.rec_on H₁ (λ Hc, absurd true.intro (if_pos Hc ▸ H₂)) (λ Hnc, Hnc)

theorem not_of_is_false {c : Prop} [H₁ : decidable c] (H₂ : is_false c) : ¬ c :=
decidable.rec_on H₁ (λ Hc, false_elim (if_pos Hc ▸ H₂)) (λ Hnc, Hnc)

theorem of_not_is_false {c : Prop} [H₁ : decidable c] (H₂ : ¬ is_false c) : c :=
decidable.rec_on H₁ (λ Hc, Hc) (λ Hnc, absurd true.intro (if_neg Hnc ▸ H₂))
