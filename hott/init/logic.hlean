/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

prelude
import init.reserved_notation

/- not -/

definition not (a : Type) := a → empty
prefix `¬` := not

definition absurd {a b : Type} (H₁ : a) (H₂ : ¬a) : b :=
empty.rec (λ e, b) (H₂ H₁)

definition mt {a b : Type} (H₁ : a → b) (H₂ : ¬b) : ¬a :=
assume Ha : a, absurd (H₁ Ha) H₂

protected definition not_empty : ¬ empty :=
assume H : empty, H

definition not_not_intro {a : Type} (Ha : a) : ¬¬a :=
assume Hna : ¬a, absurd Ha Hna

definition not.elim {a : Type} (H₁ : ¬a) (H₂ : a) : empty := H₁ H₂

definition not.intro {a : Type} (H : a → empty) : ¬a := H

definition not_not_of_not_implies {a b : Type} (H : ¬(a → b)) : ¬¬a :=
assume Hna : ¬a, absurd (assume Ha : a, absurd Ha Hna) H

definition not_of_not_implies {a b : Type} (H : ¬(a → b)) : ¬b :=
assume Hb : b, absurd (assume Ha : a, Hb) H

/- eq -/

notation a = b := eq a b
definition rfl {A : Type} {a : A} := eq.refl a

namespace eq
  variables {A : Type} {a b c : A}

  definition subst [unfold 5] {P : A → Type} (H₁ : a = b) (H₂ : P a) : P b :=
  eq.rec H₂ H₁

  definition trans [unfold 5] (H₁ : a = b) (H₂ : b = c) : a = c :=
  subst H₂ H₁

  definition symm [unfold 4] (H : a = b) : b = a :=
  subst H (refl a)

  namespace ops
    notation H `⁻¹` := symm H --input with \sy or \-1 or \inv
    notation H1 ⬝ H2 := trans H1 H2
    notation H1 ▸ H2 := subst H1 H2
  end ops
end eq

definition congr {A B : Type} {f₁ f₂ : A → B} {a₁ a₂ : A} (H₁ : f₁ = f₂) (H₂ : a₁ = a₂) : f₁ a₁ = f₂ a₂ :=
eq.subst H₁ (eq.subst H₂ rfl)

theorem congr_arg {A B : Type} (a a' : A) (f : A → B) (Ha : a = a') : f a = f a' :=
eq.subst Ha rfl

theorem congr_arg2 {A B C : Type} (a a' : A) (b b' : B) (f : A → B → C) (Ha : a = a') (Hb : b = b') : f a b = f a' b' :=
eq.subst Ha (eq.subst Hb rfl)

section
  variables {A : Type} {a b c: A}
  open eq.ops

  definition trans_rel_left (R : A → A → Type) (H₁ : R a b) (H₂ : b = c) : R a c :=
  H₂ ▸ H₁

  definition trans_rel_right (R : A → A → Type) (H₁ : a = b) (H₂ : R b c) : R a c :=
  H₁⁻¹ ▸ H₂
end

attribute eq.subst [subst]
attribute eq.refl [refl]
attribute eq.trans [trans]
attribute eq.symm [symm]

namespace lift
  definition down_up.{l₁ l₂} {A : Type.{l₁}} (a : A) : down (up.{l₁ l₂} a) = a :=
  rfl

  definition up_down.{l₁ l₂} {A : Type.{l₁}} (a : lift.{l₁ l₂} A) : up (down a) = a :=
  lift.rec_on a (λ d, rfl)
end lift

/- ne -/

definition ne {A : Type} (a b : A) := ¬(a = b)
notation a ≠ b := ne a b

namespace ne
  open eq.ops
  variable {A : Type}
  variables {a b : A}

  definition intro : (a = b → empty) → a ≠ b :=
  assume H, H

  definition elim : a ≠ b → a = b → empty :=
  assume H₁ H₂, H₁ H₂

  definition irrefl : a ≠ a → empty :=
  assume H, H rfl

  definition symm : a ≠ b → b ≠ a :=
  assume (H : a ≠ b) (H₁ : b = a), H H₁⁻¹
end ne

section
  open eq.ops
  variables {A : Type} {a b c : A}

  definition false.of_ne : a ≠ a → empty :=
  assume H, H rfl

  definition ne.of_eq_of_ne : a = b → b ≠ c → a ≠ c :=
  assume H₁ H₂, H₁⁻¹ ▸ H₂

  definition ne.of_ne_of_eq : a ≠ b → b = c → a ≠ c :=
  assume H₁ H₂, H₂ ▸ H₁
end

/- iff -/

definition iff (a b : Type) := prod (a → b) (b → a)

notation a <-> b := iff a b
notation a ↔ b := iff a b

namespace iff
  variables {a b c : Type}

  definition def : (a ↔ b) = (prod (a → b) (b → a)) :=
  rfl

  definition intro (H₁ : a → b) (H₂ : b → a) : a ↔ b :=
  prod.mk H₁ H₂

  definition elim (H₁ : (a → b) → (b → a) → c) (H₂ : a ↔ b) : c :=
  prod.rec H₁ H₂

  definition elim_left (H : a ↔ b) : a → b :=
  elim (assume H₁ H₂, H₁) H

  definition mp := @elim_left

  definition elim_right (H : a ↔ b) : b → a :=
  elim (assume H₁ H₂, H₂) H

  definition mp' := @elim_right

  definition flip_sign (H₁ : a ↔ b) : ¬a ↔ ¬b :=
  intro
    (assume Hna, mt (elim_right H₁) Hna)
    (assume Hnb, mt (elim_left H₁) Hnb)

  definition refl (a : Type) : a ↔ a :=
  intro (assume H, H) (assume H, H)

  definition rfl {a : Type} : a ↔ a :=
  refl a

  definition trans (H₁ : a ↔ b) (H₂ : b ↔ c) : a ↔ c :=
  intro
    (assume Ha, elim_left H₂ (elim_left H₁ Ha))
    (assume Hc, elim_right H₁ (elim_right H₂ Hc))

  definition symm (H : a ↔ b) : b ↔ a :=
  intro
    (assume Hb, elim_right H Hb)
    (assume Ha, elim_left H Ha)

  definition true_elim (H : a ↔ unit) : a :=
  mp (symm H) unit.star

  definition false_elim (H : a ↔ empty) : ¬a :=
  assume Ha : a, mp H Ha

  open eq.ops
  definition of_eq {a b : Type} (H : a = b) : a ↔ b :=
  iff.intro (λ Ha, H ▸ Ha) (λ Hb, H⁻¹ ▸ Hb)

  definition pi_iff_pi {A : Type} {P Q : A → Type} (H : Πa, (P a ↔ Q a)) : (Πa, P a) ↔ Πa, Q a :=
  iff.intro (λp a, iff.elim_left (H a) (p a)) (λq a, iff.elim_right (H a) (q a))

  theorem imp_iff {P : Type} (Q : Type) (p : P) : (P → Q) ↔ Q :=
  iff.intro (λf, f p) (λq p, q)

end iff

attribute iff.refl [refl]
attribute iff.trans [trans]
attribute iff.symm [symm]

/- inhabited -/

inductive inhabited [class] (A : Type) : Type :=
mk : A → inhabited A

namespace inhabited

protected definition destruct {A : Type} {B : Type} (H1 : inhabited A) (H2 : A → B) : B :=
inhabited.rec H2 H1

definition inhabited_fun [instance] (A : Type) {B : Type} [H : inhabited B] : inhabited (A → B) :=
inhabited.destruct H (λb, mk (λa, b))

definition inhabited_Pi [instance] (A : Type) {B : A → Type} [H : Πx, inhabited (B x)] :
  inhabited (Πx, B x) :=
mk (λa, inhabited.destruct (H a) (λb, b))

definition default (A : Type) [H : inhabited A] : A := inhabited.destruct H (take a, a)

end inhabited

/- decidable -/

inductive decidable.{l} [class] (p : Type.{l}) : Type.{l} :=
| inl :  p → decidable p
| inr : ¬p → decidable p

namespace decidable
  variables {p q : Type}

  definition pos_witness [C : decidable p] (H : p) : p :=
  decidable.rec_on C (λ Hp, Hp) (λ Hnp, absurd H Hnp)

  definition neg_witness [C : decidable p] (H : ¬ p) : ¬ p :=
  decidable.rec_on C (λ Hp, absurd Hp H) (λ Hnp, Hnp)

  definition by_cases {q : Type} [C : decidable p] (Hpq : p → q) (Hnpq : ¬p → q) : q :=
  decidable.rec_on C (assume Hp, Hpq Hp) (assume Hnp, Hnpq Hnp)

  definition em (p : Type) [H : decidable p] : sum p ¬p :=
  by_cases (λ Hp, sum.inl Hp) (λ Hnp, sum.inr Hnp)

  definition by_contradiction [Hp : decidable p] (H : ¬p → empty) : p :=
  by_cases
    (assume H₁ : p, H₁)
    (assume H₁ : ¬p, empty.rec (λ e, p) (H H₁))

  definition decidable_iff_equiv (Hp : decidable p) (H : p ↔ q) : decidable q :=
  decidable.rec_on Hp
    (assume Hp : p,   inl (iff.elim_left H Hp))
    (assume Hnp : ¬p, inr (iff.elim_left (iff.flip_sign H) Hnp))

  definition decidable_eq_equiv.{l} {p q : Type.{l}} (Hp : decidable p) (H : p = q) : decidable q :=
  decidable_iff_equiv Hp (iff.of_eq H)
end decidable

section
  variables {p q : Type}
  open decidable (rec_on inl inr)

  definition decidable_unit [instance] : decidable unit :=
  inl unit.star

  definition decidable_empty [instance] : decidable empty :=
  inr not_empty

  definition decidable_prod [instance] [Hp : decidable p] [Hq : decidable q] : decidable (prod p q) :=
  rec_on Hp
    (assume Hp  : p, rec_on Hq
      (assume Hq  : q,  inl (prod.mk Hp Hq))
      (assume Hnq : ¬q, inr (λ H : prod p q, prod.rec_on H (λ Hp Hq, absurd Hq Hnq))))
    (assume Hnp : ¬p, inr (λ H : prod p q, prod.rec_on H (λ Hp Hq, absurd Hp Hnp)))

  definition decidable_sum [instance] [Hp : decidable p] [Hq : decidable q] : decidable (sum p q) :=
  rec_on Hp
    (assume Hp  : p, inl (sum.inl Hp))
    (assume Hnp : ¬p, rec_on Hq
      (assume Hq  : q,  inl (sum.inr Hq))
      (assume Hnq : ¬q, inr (λ H : sum p q, sum.rec_on H (λ Hp, absurd Hp Hnp) (λ Hq, absurd Hq Hnq))))

  definition decidable_not [instance] [Hp : decidable p] : decidable (¬p) :=
  rec_on Hp
    (assume Hp,  inr (not_not_intro Hp))
    (assume Hnp, inl Hnp)

  definition decidable_implies [instance] [Hp : decidable p] [Hq : decidable q] : decidable (p → q) :=
  rec_on Hp
    (assume Hp  : p, rec_on Hq
      (assume Hq  : q,  inl (assume H, Hq))
      (assume Hnq : ¬q, inr (assume H : p → q, absurd (H Hp) Hnq)))
    (assume Hnp : ¬p, inl (assume Hp, absurd Hp Hnp))

  definition decidable_if [instance] [Hp : decidable p] [Hq : decidable q] : decidable (p ↔ q) :=
  show decidable (prod (p → q) (q → p)), from _
end

definition decidable_pred [reducible] {A : Type} (R : A   →   Type) := Π (a   : A), decidable (R a)
definition decidable_rel  [reducible] {A : Type} (R : A → A → Type) := Π (a b : A), decidable (R a b)
definition decidable_eq   [reducible] (A : Type) := decidable_rel (@eq A)
definition decidable_ne [instance] {A : Type} [H : decidable_eq A] : decidable_rel (@ne A) :=
show Π x y : A, decidable (x = y → empty), from _

definition ite (c : Type) [H : decidable c] {A : Type} (t e : A) : A :=
decidable.rec_on H (λ Hc, t) (λ Hnc, e)

definition if_pos {c : Type} [H : decidable c] (Hc : c) {A : Type} {t e : A} : (if c then t else e) = t :=
decidable.rec
  (λ Hc : c,    eq.refl (@ite c (decidable.inl Hc) A t e))
  (λ Hnc : ¬c,  absurd Hc Hnc)
  H

definition if_neg {c : Type} [H : decidable c] (Hnc : ¬c) {A : Type} {t e : A} : (if c then t else e) = e :=
decidable.rec
  (λ Hc : c,    absurd Hc Hnc)
  (λ Hnc : ¬c,  eq.refl (@ite c (decidable.inr Hnc) A t e))
  H

definition if_t_t (c : Type) [H : decidable c] {A : Type} (t : A) : (if c then t else t) = t :=
decidable.rec
  (λ Hc  : c,  eq.refl (@ite c (decidable.inl Hc)  A t t))
  (λ Hnc : ¬c, eq.refl (@ite c (decidable.inr Hnc) A t t))
  H

definition if_unit {A : Type} (t e : A) : (if unit then t else e) = t :=
if_pos unit.star

definition if_empty {A : Type} (t e : A) : (if empty then t else e) = e :=
if_neg not_empty

section
open eq.ops
definition if_cond_congr {c₁ c₂ : Type} [H₁ : decidable c₁] [H₂ : decidable c₂] (Heq : c₁ ↔ c₂) {A : Type} (t e : A)
                      : (if c₁ then t else e) = (if c₂ then t else e) :=
decidable.rec_on H₁
 (λ Hc₁  : c₁,  decidable.rec_on H₂
   (λ Hc₂  : c₂,  if_pos Hc₁ ⬝ (if_pos Hc₂)⁻¹)
   (λ Hnc₂ : ¬c₂, absurd (iff.elim_left Heq Hc₁) Hnc₂))
 (λ Hnc₁ : ¬c₁, decidable.rec_on H₂
   (λ Hc₂  : c₂,  absurd (iff.elim_right Heq Hc₂) Hnc₁)
   (λ Hnc₂ : ¬c₂, if_neg Hnc₁ ⬝ (if_neg Hnc₂)⁻¹))

definition if_congr_aux {c₁ c₂ : Type} [H₁ : decidable c₁] [H₂ : decidable c₂] {A : Type} {t₁ t₂ e₁ e₂ : A}
                     (Hc : c₁ ↔ c₂) (Ht : t₁ = t₂) (He : e₁ = e₂) :
                 (if c₁ then t₁ else e₁) = (if c₂ then t₂ else e₂) :=
Ht ▸ He ▸ (if_cond_congr Hc t₁ e₁)

definition if_congr {c₁ c₂ : Type} [H₁ : decidable c₁] {A : Type} {t₁ t₂ e₁ e₂ : A} (Hc : c₁ ↔ c₂) (Ht : t₁ = t₂) (He : e₁ = e₂) :
                 (if c₁ then t₁ else e₁) = (@ite c₂ (decidable.decidable_iff_equiv H₁ Hc) A t₂ e₂) :=
have H2 [visible] : decidable c₂, from (decidable.decidable_iff_equiv H₁ Hc),
if_congr_aux Hc Ht He

theorem implies_of_if_pos {c t e : Type} [H : decidable c] (h : if c then t else e) : c → t :=
assume Hc, eq.rec_on (if_pos Hc) h

theorem implies_of_if_neg {c t e : Type} [H : decidable c] (h : if c then t else e) : ¬c → e :=
assume Hnc, eq.rec_on (if_neg Hnc) h

-- We use "dependent" if-then-else to be able to communicate the if-then-else condition
-- to the branches
definition dite (c : Type) [H : decidable c] {A : Type} (t : c → A) (e : ¬ c → A) : A :=
decidable.rec_on H (λ Hc, t Hc) (λ Hnc, e Hnc)

definition dif_pos {c : Type} [H : decidable c] (Hc : c) {A : Type} {t : c → A} {e : ¬ c → A} : (if H : c then t H else e H) = t (decidable.pos_witness Hc) :=
decidable.rec
  (λ Hc : c,    eq.refl (@dite c (decidable.inl Hc) A t e))
  (λ Hnc : ¬c,  absurd Hc Hnc)
  H

definition dif_neg {c : Type} [H : decidable c] (Hnc : ¬c) {A : Type} {t : c → A} {e : ¬ c → A} : (if H : c then t H else e H) = e (decidable.neg_witness Hnc) :=
decidable.rec
  (λ Hc : c,    absurd Hc Hnc)
  (λ Hnc : ¬c,  eq.refl (@dite c (decidable.inr Hnc) A t e))
  H

-- Remark: dite and ite are "definitionally equal" when we ignore the proofs.
definition dite_ite_eq (c : Type) [H : decidable c] {A : Type} (t : A) (e : A) : dite c (λh, t) (λh, e) = ite c t e :=
rfl
end
open eq.ops unit

definition is_unit (c : Type) [H : decidable c] : Type₀ :=
if c then unit else empty

definition is_empty (c : Type) [H : decidable c] : Type₀ :=
if c then empty else unit

theorem of_is_unit {c : Type} [H₁ : decidable c] (H₂ : is_unit c) : c :=
decidable.rec_on H₁ (λ Hc, Hc) (λ Hnc, empty.rec _ (if_neg Hnc ▸ H₂))

notation `dec_trivial` := of_is_unit star

theorem not_of_not_is_unit {c : Type} [H₁ : decidable c] (H₂ : ¬ is_unit c) : ¬ c :=
decidable.rec_on H₁ (λ Hc, absurd star (if_pos Hc ▸ H₂)) (λ Hnc, Hnc)

theorem not_of_is_empty {c : Type} [H₁ : decidable c] (H₂ : is_empty c) : ¬ c :=
decidable.rec_on H₁ (λ Hc, empty.rec _ (if_pos Hc ▸ H₂)) (λ Hnc, Hnc)

theorem of_not_is_empty {c : Type} [H₁ : decidable c] (H₂ : ¬ is_empty c) : c :=
decidable.rec_on H₁ (λ Hc, Hc) (λ Hnc, absurd star (if_neg Hnc ▸ H₂))
