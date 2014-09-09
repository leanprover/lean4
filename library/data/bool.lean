-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura

import logic.core.connectives logic.classes.decidable logic.classes.inhabited

open eq_ops eq decidable

inductive bool : Type :=
  ff : bool,
  tt : bool
namespace bool
  definition rec_on [protected] {C : bool → Type} (b : bool) (H₁ : C ff) (H₂ : C tt) : C b :=
  rec H₁ H₂ b

  theorem cases_on [protected] {p : bool → Prop} (b : bool) (H₁ : p ff) (H₂ : p tt) : p b :=
  rec H₁ H₂ b

  definition cond {A : Type} (b : bool) (t e : A) :=
  rec_on b e t

  theorem dichotomy (b : bool) : b = ff ∨ b = tt :=
  cases_on b (or.inl rfl) (or.inr rfl)

  theorem cond_ff {A : Type} (t e : A) : cond ff t e = e :=
  rfl

  theorem cond_tt {A : Type} (t e : A) : cond tt t e = t :=
  rfl

  theorem ff_ne_tt : ¬ ff = tt :=
  assume H : ff = tt, absurd
    (calc true  = cond tt true false : (cond_tt _ _)⁻¹
            ... = cond ff true false : {H⁻¹}
            ... = false              : cond_ff _ _)
    true_ne_false

  definition bor (a b : bool) :=
  rec_on a (rec_on b ff tt) tt

  theorem bor_tt_left (a : bool) : bor tt a = tt :=
  rfl

  infixl `||` := bor

  theorem bor_tt_right (a : bool) : a || tt = tt :=
  cases_on a rfl rfl

  theorem bor_ff_left (a : bool) : ff || a = a :=
  cases_on a rfl rfl

  theorem bor_ff_right (a : bool) : a || ff = a :=
  cases_on a rfl rfl

  theorem bor_id (a : bool) : a || a = a :=
  cases_on a rfl rfl

  theorem bor_comm (a b : bool) : a || b = b || a :=
  cases_on a
    (cases_on b rfl rfl)
    (cases_on b rfl rfl)

  theorem bor_assoc (a b c : bool) : (a || b) || c = a || (b || c) :=
  cases_on a
    (calc (ff || b) || c = b || c         : {bor_ff_left b}
                   ...   = ff || (b || c) : bor_ff_left (b || c)⁻¹)
    (calc (tt || b) || c = tt || c        : {bor_tt_left b}
                   ...   = tt             : bor_tt_left c
                   ...   = tt || (b || c) : bor_tt_left (b || c)⁻¹)

  theorem bor_to_or {a b : bool} : a || b = tt → a = tt ∨ b = tt :=
  rec_on a
    (assume H : ff || b = tt,
      have Hb : b = tt, from (bor_ff_left b) ▸ H,
      or.inr Hb)
    (assume H, or.inl rfl)

  definition band (a b : bool) :=
  rec_on a ff (rec_on b ff tt)

  infixl `&&` := band

  theorem band_ff_left (a : bool) : ff && a = ff :=
  rfl

  theorem band_tt_left (a : bool) : tt && a = a :=
  cases_on a rfl rfl

  theorem band_ff_right (a : bool) : a && ff = ff :=
  cases_on a rfl rfl

  theorem band_tt_right (a : bool) : a && tt = a :=
  cases_on a rfl rfl

  theorem band_id (a : bool) : a && a = a :=
  cases_on a rfl rfl

  theorem band_comm (a b : bool) : a && b = b && a :=
  cases_on a
    (cases_on b rfl rfl)
    (cases_on b rfl rfl)

  theorem band_assoc (a b c : bool) : (a && b) && c = a && (b && c) :=
  cases_on a
    (calc (ff && b) && c = ff && c        : {band_ff_left b}
                    ...  = ff             : band_ff_left c
                    ...  = ff && (b && c) : band_ff_left (b && c)⁻¹)
    (calc (tt && b) && c = b && c         : {band_tt_left b}
                    ...  = tt && (b && c) : band_tt_left (b && c)⁻¹)

  theorem band_eq_tt_elim_left {a b : bool} (H : a && b = tt) : a = tt :=
  or.elim (dichotomy a)
    (assume H0 : a = ff,
      absurd
        (calc ff = ff && b : (band_ff_left _)⁻¹
             ... = a && b  : {H0⁻¹}
             ... = tt      : H)
        ff_ne_tt)
    (assume H1 : a = tt, H1)

  theorem band_eq_tt_elim_right {a b : bool} (H : a && b = tt) : b = tt :=
  band_eq_tt_elim_left (band_comm b a ⬝ H)

  definition bnot (a : bool) :=
  rec_on a tt ff

  notation `!` x:max := bnot x

  theorem bnot_bnot (a : bool) : !!a = a :=
  cases_on a rfl rfl

  theorem bnot_false : !ff = tt :=
  rfl

  theorem bnot_true  : !tt = ff :=
  rfl

  theorem is_inhabited [protected] [instance] : inhabited bool :=
  inhabited.mk ff

  theorem has_decidable_eq [protected] [instance] : decidable_eq bool :=
  take a b : bool,
    rec_on a
      (rec_on b (inl rfl) (inr ff_ne_tt))
      (rec_on b (inr (ne.symm ff_ne_tt)) (inl rfl))
end bool
