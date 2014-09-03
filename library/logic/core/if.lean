----------------------------------------------------------------------------------------------------
-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
----------------------------------------------------------------------------------------------------

import logic.classes.decidable tools.tactic
open decidable tactic eq_ops

definition ite (c : Prop) {H : decidable c} {A : Type} (t e : A) : A :=
decidable.rec_on H (assume Hc,  t) (assume Hnc, e)

notation `if` c `then` t `else` e:45 := ite c t e

theorem if_pos {c : Prop} {H : decidable c} (Hc : c) {A : Type} {t e : A} : (if c then t else e) = t :=
decidable_rec
  (assume Hc : c,    refl (@ite c (inl Hc) A t e))
  (assume Hnc : ¬c,  absurd Hc Hnc)
  H

theorem if_neg {c : Prop} {H : decidable c} (Hnc : ¬c) {A : Type} {t e : A} : (if c then t else e) = e :=
decidable_rec
  (assume Hc : c,    absurd Hc Hnc)
  (assume Hnc : ¬c,  refl (@ite c (inr Hnc) A t e))
  H

theorem if_t_t (c : Prop) {H : decidable c} {A : Type} (t : A) : (if c then t else t) = t :=
decidable_rec
  (assume Hc  : c,  refl (@ite c (inl Hc)  A t t))
  (assume Hnc : ¬c, refl (@ite c (inr Hnc) A t t))
  H

theorem if_true {A : Type} (t e : A) : (if true then t else e) = t :=
if_pos trivial

theorem if_false {A : Type} (t e : A) : (if false then t else e) = e :=
if_neg not_false_trivial

theorem if_cond_congr {c₁ c₂ : Prop} {H₁ : decidable c₁} {H₂ : decidable c₂} (Heq : c₁ ↔ c₂) {A : Type} (t e : A)
                      : (if c₁ then t else e) = (if c₂ then t else e) :=
decidable.rec_on H₁
 (assume Hc₁  : c₁,  decidable.rec_on H₂
   (assume Hc₂  : c₂,  if_pos Hc₁ ⬝ (if_pos Hc₂)⁻¹)
   (assume Hnc₂ : ¬c₂, absurd (iff_elim_left Heq Hc₁) Hnc₂))
 (assume Hnc₁ : ¬c₁, decidable.rec_on H₂
   (assume Hc₂  : c₂,  absurd (iff_elim_right Heq Hc₂) Hnc₁)
   (assume Hnc₂ : ¬c₂, if_neg Hnc₁ ⬝ (if_neg Hnc₂)⁻¹))

theorem if_congr_aux {c₁ c₂ : Prop} {H₁ : decidable c₁} {H₂ : decidable c₂} {A : Type} {t₁ t₂ e₁ e₂ : A}
                     (Hc : c₁ ↔ c₂) (Ht : t₁ = t₂) (He : e₁ = e₂) :
                 (if c₁ then t₁ else e₁) = (if c₂ then t₂ else e₂) :=
Ht ▸ He ▸ (if_cond_congr Hc t₁ e₁)

theorem if_congr {c₁ c₂ : Prop} {H₁ : decidable c₁} {A : Type} {t₁ t₂ e₁ e₂ : A} (Hc : c₁ ↔ c₂) (Ht : t₁ = t₂) (He : e₁ = e₂) :
                 (if c₁ then t₁ else e₁) = (@ite c₂ (decidable_iff_equiv H₁ Hc) A t₂ e₂) :=
have H2 [fact] : decidable c₂, from (decidable_iff_equiv H₁ Hc),
if_congr_aux Hc Ht He
