----------------------------------------------------------------------------------------------------
-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
----------------------------------------------------------------------------------------------------

import logic.classes.decidable tools.tactic
using decidable tactic eq_proofs

definition ite (c : Prop) {H : decidable c} {A : Type} (t e : A) : A :=
rec_on H (assume Hc,  t) (assume Hnc, e)

notation `if` c `then` t `else` e:45 := ite c t e

theorem if_pos {c : Prop} {H : decidable c} (Hc : c) {A : Type} (t e : A) : (if c then t else e) = t :=
decidable_rec
  (assume Hc : c,    refl (@ite c (inl Hc) A t e))
  (assume Hnc : ¬c,  absurd_elim (@ite c (inr Hnc) A t e = t) Hc Hnc)
  H

theorem if_neg {c : Prop} {H : decidable c} (Hnc : ¬c) {A : Type} (t e : A) : (if c then t else e) = e :=
decidable_rec
  (assume Hc : c,    absurd_elim (@ite c (inl Hc) A t e = e) Hc Hnc)
  (assume Hnc : ¬c,  refl (@ite c (inr Hnc) A t e))
  H

theorem if_t_t (c : Prop) {H : decidable c} {A : Type} (t : A) : (if c then t else t) = t :=
decidable_rec
  (assume Hc  : c,  refl (@ite c (inl Hc)  A t t))
  (assume Hnc : ¬c, refl (@ite c (inr Hnc) A t t))
  H

theorem if_true {A : Type} (t e : A) : (if true then t else e) = t :=
if_pos trivial t e

theorem if_false {A : Type} (t e : A) : (if false then t else e) = e :=
if_neg not_false_trivial t e

theorem if_congr_aux {c₁ c₂ : Prop} {H₁ : decidable c₁} {H₂ : decidable c₂} {A : Type} {t₁ t₂ e₁ e₂ : A}
                     (Hc : c₁ = c₂) (Ht : t₁ = t₂) (He : e₁ = e₂) :
                 (if c₁ then t₁ else e₁) = (if c₂ then t₂ else e₂) :=
have H1 : ∀ (H : decidable c₁), (@ite c₁ H₁ A t₁ e₁) = (@ite c₁ H A t₁ e₁), from
  take H : decidable c₁,
    have Hd : H₁ = H, from irrelevant H₁ H,
    Hd ▸ refl (@ite c₁ H₁ A t₁ e₁),
have H2 : (@ite c₁ H₁ A t₁ e₁) = (@ite c₂ H₂ A t₁ e₁), from
  (Hc ▸ H1) H₂,
Ht ▸ He ▸ H2

theorem if_congr {c₁ c₂ : Prop} {H₁ : decidable c₁} {A : Type} {t₁ t₂ e₁ e₂ : A} (Hc : c₁ = c₂) (Ht : t₁ = t₂) (He : e₁ = e₂) :
                 (if c₁ then t₁ else e₁) = (@ite c₂ (decidable_eq_equiv H₁ Hc) A t₂ e₂) :=
have H2 [fact] : decidable c₂, from (decidable_eq_equiv H₁ Hc),
if_congr_aux Hc Ht He
