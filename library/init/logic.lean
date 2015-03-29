/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: init.logic
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
-/
prelude
import init.datatypes init.reserved_notation

/- implication -/

definition trivial := true.intro

definition not (a : Prop) := a → false
prefix `¬` := not

definition absurd {a : Prop} {b : Type} (H1 : a) (H2 : ¬a) : b :=
false.rec b (H2 H1)

/- not -/

theorem not_false : ¬false :=
assume H : false, H

/- eq -/

notation a = b := eq a b
definition rfl {A : Type} {a : A} := eq.refl a

-- proof irrelevance is built in
theorem proof_irrel {a : Prop} (H₁ H₂ : a) : H₁ = H₂ :=
rfl

namespace eq
  variables {A : Type}
  variables {a b c a': A}

  theorem subst {P : A → Prop} (H₁ : a = b) (H₂ : P a) : P b :=
  eq.rec H₂ H₁

  theorem trans (H₁ : a = b) (H₂ : b = c) : a = c :=
  subst H₂ H₁

  definition symm (H : a = b) : b = a :=
  eq.rec (refl a) H

  namespace ops
    notation H `⁻¹` := symm H --input with \sy or \-1 or \inv
    notation H1 ⬝ H2 := trans H1 H2
    notation H1 ▸ H2 := subst H1 H2
  end ops

end eq

section
  variable {p : Prop}
  open eq.ops

  theorem of_eq_true (H : p = true) : p :=
  H⁻¹ ▸ trivial

  theorem not_of_eq_false (H : p = false) : ¬p :=
  assume Hp, H ▸ Hp
end

calc_subst eq.subst
calc_refl  eq.refl
calc_trans eq.trans
calc_symm  eq.symm

/- ne -/

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

  theorem subst {P : ∀T : Type, T → Prop} (H₁ : a == b) (H₂ : P A a) : P B b :=
  heq.rec_on H₁ H₂

  theorem symm (H : a == b) : b == a :=
  heq.rec_on H (refl a)

  theorem of_eq (H : a = a') : a == a' :=
  eq.subst H (refl a)

  theorem trans (H₁ : a == b) (H₂ : b == c) : a == c :=
  subst H₂ H₁

  theorem of_heq_of_eq (H₁ : a == b) (H₂ : b = b') : a == b' :=
  trans H₁ (of_eq H₂)

  theorem of_eq_of_heq (H₁ : a = a') (H₂ : a' == b) : a == b :=
  trans (of_eq H₁) H₂
end heq

theorem of_heq_true {a : Prop} (H : a == true) : a :=
of_eq_true (heq.to_eq H)

calc_trans heq.trans
calc_trans heq.of_heq_of_eq
calc_trans heq.of_eq_of_heq
calc_symm  heq.symm

/- and -/

notation a /\ b := and a b
notation a ∧ b  := and a b

variables {a b c d : Prop}

theorem and.elim (H₁ : a ∧ b) (H₂ : a → b → c) : c :=
and.rec H₂ H₁

/- or -/

notation a `\/` b := or a b
notation a ∨ b := or a b

namespace or
  theorem elim (H₁ : a ∨ b) (H₂ : a → c) (H₃ : b → c) : c :=
  or.rec H₂ H₃ H₁
end or

/- iff -/

definition iff (a b : Prop) := (a → b) ∧ (b → a)

notation a <-> b := iff a b
notation a ↔ b := iff a b

namespace iff
  definition intro (H₁ : a → b) (H₂ : b → a) : a ↔ b :=
  and.intro H₁ H₂

  definition elim (H₁ : (a → b) → (b → a) → c) (H₂ : a ↔ b) : c :=
  and.rec H₁ H₂

  definition elim_left (H : a ↔ b) : a → b :=
  elim (assume H₁ H₂, H₁) H

  definition mp := @elim_left

  definition elim_right (H : a ↔ b) : b → a :=
  elim (assume H₁ H₂, H₂) H

  definition mp' := @elim_right

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

  open eq.ops
  theorem of_eq {a b : Prop} (H : a = b) : a ↔ b :=
  iff.intro (λ Ha, H ▸ Ha) (λ Hb, H⁻¹ ▸ Hb)
end iff

definition not_iff_not_of_iff (H₁ : a ↔ b) : ¬a ↔ ¬b :=
iff.intro
 (assume (Hna : ¬ a) (Hb : b), absurd (iff.elim_right H₁ Hb) Hna)
 (assume (Hnb : ¬ b) (Ha : a), absurd (iff.elim_left H₁ Ha) Hnb)

theorem of_iff_true (H : a ↔ true) : a :=
iff.mp (iff.symm H) trivial

theorem not_of_iff_false (H : a ↔ false) : ¬a :=
assume Ha : a, iff.mp H Ha

theorem iff_of_eq_of_iff (H₁ : a = b) (H₂ : b ↔ c) : a ↔ c :=
H₁⁻¹ ▸ H₂

theorem iff_of_iff_of_eq (H₁ : a ↔ b) (H₂ : b = c) : a ↔ c :=
H₂ ▸ H₁

calc_refl iff.refl
calc_trans iff.trans
calc_trans iff_of_eq_of_iff
calc_trans iff_of_iff_of_eq

inductive Exists {A : Type} (P : A → Prop) : Prop :=
intro : ∀ (a : A), P a → Exists P

definition exists.intro := @Exists.intro

notation `exists` binders `,` r:(scoped P, Exists P) := r
notation `∃` binders `,` r:(scoped P, Exists P) := r

theorem exists.elim {A : Type} {p : A → Prop} {B : Prop} (H1 : ∃x, p x) (H2 : ∀ (a : A) (H : p a), B) : B :=
Exists.rec H2 H1

/- decidable -/

inductive decidable [class] (p : Prop) : Type :=
| inl :  p → decidable p
| inr : ¬p → decidable p

definition decidable_true [instance] : decidable true :=
decidable.inl trivial

definition decidable_false [instance] : decidable false :=
decidable.inr not_false

namespace decidable
  variables {p q : Prop}

  definition rec_on_true [H : decidable p] {H1 : p → Type} {H2 : ¬p → Type} (H3 : p) (H4 : H1 H3)
      : decidable.rec_on H H1 H2 :=
  decidable.rec_on H (λh, H4) (λh, !false.rec (h H3))

  definition rec_on_false [H : decidable p] {H1 : p → Type} {H2 : ¬p → Type} (H3 : ¬p) (H4 : H2 H3)
      : decidable.rec_on H H1 H2 :=
  decidable.rec_on H (λh, false.rec _ (H3 h)) (λh, H4)

  definition by_cases {q : Type} [C : decidable p] (Hpq : p → q) (Hnpq : ¬p → q) : q :=
  decidable.rec_on C (assume Hp, Hpq Hp) (assume Hnp, Hnpq Hnp)

  theorem em (p : Prop) [H : decidable p] : p ∨ ¬p :=
  by_cases (λ Hp, or.inl Hp) (λ Hnp, or.inr Hnp)

  theorem by_contradiction [Hp : decidable p] (H : ¬p → false) : p :=
  by_cases
    (assume H1 : p, H1)
    (assume H1 : ¬p, false.rec _ (H H1))
end decidable

section
  variables {p q : Prop}
  open decidable
  definition  decidable_of_decidable_of_iff (Hp : decidable p) (H : p ↔ q) : decidable q :=
  decidable.rec_on Hp
    (assume Hp : p,   inl (iff.elim_left H Hp))
    (assume Hnp : ¬p, inr (iff.elim_left (not_iff_not_of_iff H) Hnp))

  definition  decidable_of_decidable_of_eq (Hp : decidable p) (H : p = q) : decidable q :=
  decidable_of_decidable_of_iff Hp (iff.of_eq H)
end

section
  variables {p q : Prop}
  open decidable (rec_on inl inr)

  definition decidable_and [instance] [Hp : decidable p] [Hq : decidable q] : decidable (p ∧ q) :=
  rec_on Hp
    (assume Hp  : p, rec_on Hq
      (assume Hq  : q,  inl (and.intro Hp Hq))
      (assume Hnq : ¬q, inr (assume H : p ∧ q, and.rec_on H (assume Hp Hq, absurd Hq Hnq))))
    (assume Hnp : ¬p, inr (assume H : p ∧ q, and.rec_on H (assume Hp Hq, absurd Hp Hnp)))

  definition decidable_or [instance] [Hp : decidable p] [Hq : decidable q] : decidable (p ∨ q) :=
  rec_on Hp
    (assume Hp  : p, inl (or.inl Hp))
    (assume Hnp : ¬p, rec_on Hq
      (assume Hq  : q,  inl (or.inr Hq))
      (assume Hnq : ¬q, inr (assume H : p ∨ q, or.elim H (assume Hp, absurd Hp Hnp) (assume Hq, absurd Hq Hnq))))

  definition decidable_not [instance] [Hp : decidable p] : decidable (¬p) :=
  rec_on Hp
    (assume Hp,  inr (λ Hnp, absurd Hp Hnp))
    (assume Hnp, inl Hnp)

  definition decidable_implies [instance] [Hp : decidable p] [Hq : decidable q] : decidable (p → q) :=
  rec_on Hp
    (assume Hp  : p, rec_on Hq
      (assume Hq  : q,  inl (assume H, Hq))
      (assume Hnq : ¬q, inr (assume H : p → q, absurd (H Hp) Hnq)))
    (assume Hnp : ¬p, inl (assume Hp, absurd Hp Hnp))

  definition decidable_iff [instance] [Hp : decidable p] [Hq : decidable q] : decidable (p ↔ q) :=
  show decidable ((p → q) ∧ (q → p)), from _

end

definition decidable_pred [reducible] {A : Type} (R : A   →   Prop) := Π (a   : A), decidable (R a)
definition decidable_rel  [reducible] {A : Type} (R : A → A → Prop) := Π (a b : A), decidable (R a b)
definition decidable_eq   [reducible] (A : Type) := decidable_rel (@eq A)
definition decidable_ne [instance] {A : Type} [H : decidable_eq A] : Π (a b : A), decidable (a ≠ b) :=
show Π x y : A, decidable (x = y → false), from _

namespace bool
  definition ff_ne_tt : ff = tt → false
  | [none]
end bool

open bool
definition is_dec_eq {A : Type} (p : A → A → bool) : Prop   := ∀ ⦃x y : A⦄, p x y = tt → x = y
definition is_dec_refl {A : Type} (p : A → A → bool) : Prop := ∀x, p x x = tt

open decidable
protected definition bool.has_decidable_eq [instance] : ∀a b : bool, decidable (a = b)
| ff ff := inl rfl
| ff tt := inr ff_ne_tt
| tt ff := inr (ne.symm ff_ne_tt)
| tt tt := inl rfl

definition decidable_eq_of_bool_pred {A : Type} {p : A → A → bool} (H₁ : is_dec_eq p) (H₂ : is_dec_refl p) : decidable_eq A :=
take x y : A, by_cases
 (assume Hp : p x y = tt,   inl (H₁ Hp))
 (assume Hn : ¬ p x y = tt, inr (assume Hxy : x = y, absurd (H₂ y) (eq.rec_on Hxy Hn)))

/- inhabited -/

inductive inhabited [class] (A : Type) : Type :=
mk : A → inhabited A

protected definition inhabited.value {A : Type} (h : inhabited A) : A :=
inhabited.rec (λa, a) h

protected definition inhabited.destruct {A : Type} {B : Type} (H1 : inhabited A) (H2 : A → B) : B :=
inhabited.rec H2 H1

definition default (A : Type) [H : inhabited A] : A :=
inhabited.rec (λa, a) H

opaque definition arbitrary (A : Type) [H : inhabited A] : A :=
inhabited.rec (λa, a) H

definition Prop.is_inhabited [instance] : inhabited Prop :=
inhabited.mk true

definition inhabited_fun [instance] (A : Type) {B : Type} [H : inhabited B] : inhabited (A → B) :=
inhabited.rec_on H (λb, inhabited.mk (λa, b))

definition inhabited_Pi [instance] (A : Type) {B : A → Type} [H : Πx, inhabited (B x)] :
  inhabited (Πx, B x) :=
inhabited.mk (λa, inhabited.rec_on (H a) (λb, b))

protected definition bool.is_inhabited [instance] : inhabited bool :=
inhabited.mk ff

inductive nonempty [class] (A : Type) : Prop :=
intro : A → nonempty A

protected definition nonempty.elim {A : Type} {B : Prop} (H1 : nonempty A) (H2 : A → B) : B :=
nonempty.rec H2 H1

theorem nonempty_of_inhabited [instance] {A : Type} [H : inhabited A] : nonempty A :=
nonempty.intro (default A)

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
decidable.rec_on H₁ (λ Hc, Hc) (λ Hnc, !false.rec (if_neg Hnc ▸ H₂))

notation `dec_trivial` := of_is_true trivial

theorem not_of_not_is_true {c : Prop} [H₁ : decidable c] (H₂ : ¬ is_true c) : ¬ c :=
decidable.rec_on H₁ (λ Hc, absurd true.intro (if_pos Hc ▸ H₂)) (λ Hnc, Hnc)

theorem not_of_is_false {c : Prop} [H₁ : decidable c] (H₂ : is_false c) : ¬ c :=
decidable.rec_on H₁ (λ Hc, !false.rec (if_pos Hc ▸ H₂)) (λ Hnc, Hnc)

theorem of_not_is_false {c : Prop} [H₁ : decidable c] (H₂ : ¬ is_false c) : c :=
decidable.rec_on H₁ (λ Hc, Hc) (λ Hnc, absurd true.intro (if_neg Hnc ▸ H₂))
