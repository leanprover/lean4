-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import logic decidable
using eq_proofs

namespace bool
inductive bool : Type :=
| b0 : bool
| b1 : bool
notation `'0`:max := b0
notation `'1`:max := b1

theorem induction_on {p : bool → Prop} (b : bool) (H0 : p '0) (H1 : p '1) : p b
:= bool_rec H0 H1 b

theorem inhabited_bool [instance] : inhabited bool
:= inhabited_intro b0

definition cond {A : Type} (b : bool) (t e : A)
:= bool_rec e t b

theorem dichotomy (b : bool) : b = '0 ∨ b = '1
:= induction_on b (or_intro_left _ (refl '0)) (or_intro_right _ (refl '1))

theorem cond_b0 {A : Type} (t e : A) : cond '0 t e = e
:= refl (cond '0 t e)

theorem cond_b1 {A : Type} (t e : A) : cond '1 t e = t
:= refl (cond '1 t e)

theorem b0_ne_b1 : ¬ '0 = '1
:= assume H : '0 = '1, absurd
    (calc true  = cond '1 true false : (cond_b1 _ _)⁻¹
           ... = cond '0 true false : {H⁻¹}
           ... = false              : cond_b0 _ _)
    true_ne_false

definition bor (a b : bool)
:= bool_rec (bool_rec '0 '1 b) '1 a

theorem bor_b1_left (a : bool) : bor '1 a = '1
:= refl (bor '1 a)

infixl `||`:65 := bor

theorem bor_b1_right (a : bool) : a || '1 = '1
:= induction_on a (refl ('0 || '1)) (refl ('1 || '1))

theorem bor_b0_left (a : bool) : '0 || a = a
:= induction_on a (refl ('0 || '0)) (refl ('0 || '1))

theorem bor_b0_right (a : bool) : a || '0 = a
:= induction_on a (refl ('0 || '0)) (refl ('1 || '0))

theorem bor_id (a : bool) : a || a = a
:= induction_on a (refl ('0 || '0)) (refl ('1 || '1))

theorem bor_swap (a b : bool) : a || b = b || a
:= induction_on a
    (induction_on b (refl ('0 || '0)) (refl ('0 || '1)))
    (induction_on b (refl ('1 || '0)) (refl ('1 || '1)))

definition band (a b : bool)
:= bool_rec '0 (bool_rec '0 '1 b) a

infixl `&&`:75 := band

theorem band_b0_left (a : bool) : '0 && a = '0
:= refl ('0 && a)

theorem band_b1_left (a : bool) : '1 && a = a
:= induction_on a (refl ('1 && '0)) (refl ('1 && '1))

theorem band_b0_right (a : bool) : a && '0 = '0
:= induction_on a (refl ('0 && '0)) (refl ('1 && '0))

theorem band_b1_right (a : bool) : a && '1 = a
:= induction_on a (refl ('0 && '1)) (refl ('1 && '1))

theorem band_id (a : bool) : a && a = a
:= induction_on a (refl ('0 && '0)) (refl ('1 && '1))

theorem band_swap (a b : bool) : a && b = b && a
:= induction_on a
    (induction_on b (refl ('0 && '0)) (refl ('0 && '1)))
    (induction_on b (refl ('1 && '0)) (refl ('1 && '1)))

theorem band_eq_b1_elim_left {a b : bool} (H : a && b = '1) : a = '1
:= or_elim (dichotomy a)
    (assume H0 : a = '0,
      absurd_elim (a = '1)
        (calc '0 = '0 && b : (band_b0_left _)⁻¹
             ... = a && b  : {H0⁻¹}
             ... = '1      : H)
         b0_ne_b1)
    (assume H1 : a = '1, H1)

theorem band_eq_b1_elim_right {a b : bool} (H : a && b = '1) : b = '1
:= band_eq_b1_elim_left (trans (band_swap b a) H)

definition bnot (a : bool) := bool_rec '1 '0 a

prefix `!`:85 := bnot

theorem bnot_bnot (a : bool) : !!a = a
:= induction_on a (refl (!!'0)) (refl (!!'1))

theorem bnot_false : !'0 = '1
:= refl _

theorem bnot_true  : !'1 = '0
:= refl _

using decidable
theorem decidable_eq [instance] (a b : bool) : decidable (a = b)
:= bool_rec
    (bool_rec (inl (refl '0)) (inr b0_ne_b1) b)
    (bool_rec (inr (not_eq_symm b0_ne_b1)) (inl (refl '1)) b)
    a
end
