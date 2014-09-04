-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura

import logic.core.connectives logic.classes.decidable logic.classes.inhabited

open eq_ops decidable

inductive bool : Type :=
ff : bool,
tt : bool

namespace bool

theorem cases_on {p : bool → Prop} (b : bool) (H0 : p ff) (H1 : p tt) : p b :=
rec H0 H1 b

theorem bool_inhabited [instance] : inhabited bool :=
inhabited_mk ff

definition cond {A : Type} (b : bool) (t e : A) :=
rec e t b

theorem dichotomy (b : bool) : b = ff ∨ b = tt :=
cases_on b (or_inl (refl ff)) (or_inr (refl tt))

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

theorem decidable_eq [instance] (a b : bool) : decidable (a = b) :=
rec
  (rec (inl (refl ff)) (inr ff_ne_tt) b)
  (rec (inr (ne_symm ff_ne_tt)) (inl (refl tt)) b)
  a

definition bor (a b : bool) :=
rec (rec ff tt b) tt a

theorem bor_tt_left (a : bool) : bor tt a = tt :=
rfl

infixl `||` := bor

theorem bor_tt_right (a : bool) : a || tt = tt :=
cases_on a (refl (ff || tt)) (refl (tt || tt))

theorem bor_ff_left (a : bool) : ff || a = a :=
cases_on a (refl (ff || ff)) (refl (ff || tt))

theorem bor_ff_right (a : bool) : a || ff = a :=
cases_on a (refl (ff || ff)) (refl (tt || ff))

theorem bor_id (a : bool) : a || a = a :=
cases_on a (refl (ff || ff)) (refl (tt || tt))

theorem bor_comm (a b : bool) : a || b = b || a :=
cases_on a
  (cases_on b (refl (ff || ff)) (refl (ff || tt)))
  (cases_on b (refl (tt || ff)) (refl (tt || tt)))

theorem bor_assoc (a b c : bool) : (a || b) || c = a || (b || c) :=
cases_on a
  (calc (ff || b) || c = b || c         : {bor_ff_left b}
                 ...   = ff || (b || c) : bor_ff_left (b || c)⁻¹)
  (calc (tt || b) || c = tt || c        : {bor_tt_left b}
                 ...   = tt             : bor_tt_left c
                 ...   = tt || (b || c) : bor_tt_left (b || c)⁻¹)

theorem bor_to_or {a b : bool} : a || b = tt → a = tt ∨ b = tt :=
rec
  (assume H : ff || b = tt,
    have Hb : b = tt, from (bor_ff_left b) ▸ H,
    or_inr Hb)
  (assume H, or_inl (refl tt))
  a

definition band (a b : bool) :=
rec ff (rec ff tt b) a

infixl `&&` := band

theorem band_ff_left (a : bool) : ff && a = ff :=
rfl

theorem band_tt_left (a : bool) : tt && a = a :=
cases_on a (refl (tt && ff)) (refl (tt && tt))

theorem band_ff_right (a : bool) : a && ff = ff :=
cases_on a (refl (ff && ff)) (refl (tt && ff))

theorem band_tt_right (a : bool) : a && tt = a :=
cases_on a (refl (ff && tt)) (refl (tt && tt))

theorem band_id (a : bool) : a && a = a :=
cases_on a (refl (ff && ff)) (refl (tt && tt))

theorem band_comm (a b : bool) : a && b = b && a :=
cases_on a
  (cases_on b (refl (ff && ff)) (refl (ff && tt)))
  (cases_on b (refl (tt && ff)) (refl (tt && tt)))

theorem band_assoc (a b c : bool) : (a && b) && c = a && (b && c) :=
cases_on a
  (calc (ff && b) && c = ff && c        : {band_ff_left b}
                  ...  = ff             : band_ff_left c
                  ...  = ff && (b && c) : band_ff_left (b && c)⁻¹)
  (calc (tt && b) && c = b && c         : {band_tt_left b}
                  ...  = tt && (b && c) : band_tt_left (b && c)⁻¹)

theorem band_eq_tt_elim_left {a b : bool} (H : a && b = tt) : a = tt :=
or_elim (dichotomy a)
  (assume H0 : a = ff,
    absurd
      (calc ff = ff && b : (band_ff_left _)⁻¹
           ... = a && b  : {H0⁻¹}
           ... = tt      : H)
      ff_ne_tt)
  (assume H1 : a = tt, H1)

theorem band_eq_tt_elim_right {a b : bool} (H : a && b = tt) : b = tt :=
band_eq_tt_elim_left (trans (band_comm b a) H)

definition bnot (a : bool) := rec tt ff a

notation `!` x:max := bnot x

theorem bnot_bnot (a : bool) : !!a = a :=
cases_on a (refl (!!ff)) (refl (!!tt))

theorem bnot_false : !ff = tt :=
rfl

theorem bnot_true  : !tt = ff :=
rfl

end bool
