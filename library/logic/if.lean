----------------------------------------------------------------------------------------------------
-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
----------------------------------------------------------------------------------------------------

import logic.decidable tools.tactic
open decidable tactic eq.ops

definition ite (c : Prop) [H : decidable c] {A : Type} (t e : A) : A :=
decidable.rec_on H (λ Hc, t) (λ Hnc, e)

notation `if` c `then` t:45 `else` e:45 := ite c t e

definition if_pos {c : Prop} [H : decidable c] (Hc : c) {A : Type} {t e : A} : (if c then t else e) = t :=
decidable.rec
  (λ Hc : c,    eq.refl (@ite c (inl Hc) A t e))
  (λ Hnc : ¬c,  absurd Hc Hnc)
  H

definition if_neg {c : Prop} [H : decidable c] (Hnc : ¬c) {A : Type} {t e : A} : (if c then t else e) = e :=
decidable.rec
  (λ Hc : c,    absurd Hc Hnc)
  (λ Hnc : ¬c,  eq.refl (@ite c (inr Hnc) A t e))
  H

definition if_t_t (c : Prop) [H : decidable c] {A : Type} (t : A) : (if c then t else t) = t :=
decidable.rec
  (λ Hc  : c,  eq.refl (@ite c (inl Hc)  A t t))
  (λ Hnc : ¬c, eq.refl (@ite c (inr Hnc) A t t))
  H

definition if_true {A : Type} (t e : A) : (if true then t else e) = t :=
if_pos trivial

definition if_false {A : Type} (t e : A) : (if false then t else e) = e :=
if_neg not_false_trivial

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
                 (if c₁ then t₁ else e₁) = (@ite c₂ (decidable_iff_equiv H₁ Hc) A t₂ e₂) :=
have H2 [visible] : decidable c₂, from (decidable_iff_equiv H₁ Hc),
if_congr_aux Hc Ht He

-- We use "dependent" if-then-else to be able to communicate the if-then-else condition
-- to the branches
definition dite (c : Prop) [H : decidable c] {A : Type} (t : c → A) (e : ¬ c → A) : A :=
decidable.rec_on H (λ Hc, t Hc) (λ Hnc, e Hnc)

notation `dif` c `then` t:45 `else` e:45 := dite c t e

definition dif_pos {c : Prop} [H : decidable c] (Hc : c) {A : Type} {t : c → A} {e : ¬ c → A} : (dif c then t else e) = t Hc :=
decidable.rec
  (λ Hc : c,    eq.refl (@dite c (inl Hc) A t e))
  (λ Hnc : ¬c,  absurd Hc Hnc)
  H

definition dif_neg {c : Prop} [H : decidable c] (Hnc : ¬c) {A : Type} {t : c → A} {e : ¬ c → A} : (dif c then t else e) = e Hnc :=
decidable.rec
  (λ Hc : c,    absurd Hc Hnc)
  (λ Hnc : ¬c,  eq.refl (@dite c (inr Hnc) A t e))
  H

-- Remark: dite and ite are "definitionally equal" when we ignore the proofs.
theorem dite_ite_eq (c : Prop) [H : decidable c] {A : Type} (t : A) (e : A) : dite c (λh, t) (λh, e) = ite c t e :=
rfl
