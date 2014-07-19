-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import logic
namespace bit
inductive bit : Type :=
| b0 : bit
| b1 : bit
notation `'0`:max := b0
notation `'1`:max := b1

theorem induction_on {p : bit → Bool} (b : bit) (H0 : p '0) (H1 : p '1) : p b
:= bit_rec H0 H1 b

theorem inhabited_bit [instance] : inhabited bit
:= inhabited_intro b0

definition cond {A : Type} (b : bit) (t e : A)
:= bit_rec e t b

theorem dichotomy (b : bit) : b = '0 ∨ b = '1
:= induction_on b (or_intro_left _ (refl '0)) (or_intro_right _ (refl '1))

theorem cond_b0 {A : Type} (t e : A) : cond '0 t e = e
:= refl (cond '0 t e)

theorem cond_b1 {A : Type} (t e : A) : cond '1 t e = t
:= refl (cond '1 t e)

theorem b0_ne_b1 : ¬ '0 = '1
:= not_intro (assume H : '0 = '1, absurd
    (calc true  = cond '1 true false : symm (cond_b1 _ _)
           ... = cond '0 true false : {symm H}
           ... = false              : cond_b0 _ _)
    true_ne_false)

definition bor (a b : bit)
:= bit_rec (bit_rec '0 '1 b) '1 a

theorem bor_b1_left (a : bit) : bor '1 a = '1
:= refl (bor '1 a)

infixl `||`:65 := bor

theorem bor_b1_right (a : bit) : a || '1 = '1
:= induction_on a (refl ('0 || '1)) (refl ('1 || '1))

theorem bor_b0_left (a : bit) : '0 || a = a
:= induction_on a (refl ('0 || '0)) (refl ('0 || '1))

theorem bor_b0_right (a : bit) : a || '0 = a
:= induction_on a (refl ('0 || '0)) (refl ('1 || '0))

theorem bor_id (a : bit) : a || a = a
:= induction_on a (refl ('0 || '0)) (refl ('1 || '1))

theorem bor_swap (a b : bit) : a || b = b || a
:= induction_on a
    (induction_on b (refl ('0 || '0)) (refl ('0 || '1)))
    (induction_on b (refl ('1 || '0)) (refl ('1 || '1)))

definition band (a b : bit)
:= bit_rec '0 (bit_rec '0 '1 b) a

infixl `&&`:75 := band

theorem band_b0_left (a : bit) : '0 && a = '0
:= refl ('0 && a)

theorem band_b1_left (a : bit) : '1 && a = a
:= induction_on a (refl ('1 && '0)) (refl ('1 && '1))

theorem band_b0_right (a : bit) : a && '0 = '0
:= induction_on a (refl ('0 && '0)) (refl ('1 && '0))

theorem band_b1_right (a : bit) : a && '1 = a
:= induction_on a (refl ('0 && '1)) (refl ('1 && '1))

theorem band_id (a : bit) : a && a = a
:= induction_on a (refl ('0 && '0)) (refl ('1 && '1))

theorem band_swap (a b : bit) : a && b = b && a
:= induction_on a
    (induction_on b (refl ('0 && '0)) (refl ('0 && '1)))
    (induction_on b (refl ('1 && '0)) (refl ('1 && '1)))

theorem band_eq_b1_elim_left {a b : bit} (H : a && b = '1) : a = '1
:= or_elim (dichotomy a)
    (assume H0 : a = '0,
      absurd_elim (a = '1)
        (calc '0 = '0 && b : symm (band_b0_left _)
             ... = a && b  : {symm H0}
             ... = '1      : H)
         b0_ne_b1)
    (assume H1 : a = '1, H1)

theorem band_eq_b1_elim_right {a b : bit} (H : a && b = '1) : b = '1
:= band_eq_b1_elim_left (trans (band_swap b a) H)

definition bnot (a : bit) := bit_rec '1 '0 a

prefix `!`:85 := bnot

theorem bnot_bnot (a : bit) : !!a = a
:= induction_on a (refl (!!'0)) (refl (!!'1))

theorem bnot_false : !'0 = '1
:= refl _

theorem bnot_true  : !'1 = '0
:= refl _

definition beq (a b : bit) : bit
:= bit_rec (bit_rec '1 '0 b) (bit_rec '0 '1 b) a

infix `==`:50 := beq

theorem beq_refl (a : bit) : (a == a) = '1
:= induction_on a (refl ('0 == '0)) (refl ('1 == '1))

theorem beq_b1_left (a : bit) : ('1 == a) = a
:= induction_on a (refl ('1 == '0)) (refl ('1 == '1))

theorem beq_b1_right (a : bit) : (a == '1) = a
:= induction_on a (refl ('0 == '1)) (refl ('1 == '1))

theorem beq_symm (a b : bit) : (a == b) = (b == a)
:= induction_on a
    (induction_on b (refl ('0 == '0)) (refl ('0 == '1)))
    (induction_on b (refl ('1 == '0)) (refl ('1 == '1)))

theorem to_eq {a b : bit} : a == b = '1 → a = b
:= induction_on a
    (induction_on b (assume H, refl '0) (assume H, absurd_elim ('0 = '1) (trans (symm (beq_b1_right '0)) H) b0_ne_b1))
    (induction_on b (assume H, absurd_elim ('1 = '0) (trans (symm (beq_b1_left '0)) H) b0_ne_b1) (assume H, refl '1))

theorem beq_eq (a b : bit) : (a == b) = '1 ↔ a = b
:= iff_intro
    (assume H, to_eq H)
    (assume H, subst H (beq_refl a))
end
