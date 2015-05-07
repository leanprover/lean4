/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: types.int.hott
Author: Floris van Doorn

Theorems about the integers specific to HoTT
-/

import .basic types.eq
open core is_equiv equiv equiv.ops
open nat (hiding pred)

namespace int

  definition succ (a : ℤ) := a + (nat.succ zero)
  definition pred (a : ℤ) := a - (nat.succ zero)
  definition pred_succ (a : ℤ) : pred (succ a) = a := !sub_add_cancel
  definition pred_nat_succ (n : ℕ) : pred (nat.succ n) = n := pred_succ n
  definition succ_pred (a : ℤ) : succ (pred a) = a := !add_sub_cancel
  definition neg_succ (a : ℤ) : -succ a = pred (-a) :=
  by rewrite [↑succ,neg_add]
  definition succ_neg_succ (a : ℤ) : succ (-succ a) = -a :=
  by rewrite [neg_succ,succ_pred]
  definition neg_pred (a : ℤ) : -pred a = succ (-a) :=
  by rewrite [↑pred,neg_sub,sub_eq_add_neg,add.comm]
  definition pred_neg_pred (a : ℤ) : pred (-pred a) = -a :=
  by rewrite [neg_pred,pred_succ]

  definition is_equiv_succ [instance] : is_equiv succ :=
  adjointify succ pred (λa, !add_sub_cancel) (λa, !sub_add_cancel)
  definition equiv_succ : ℤ ≃ ℤ := equiv.mk succ _

  definition is_equiv_neg [instance] : is_equiv neg :=
  adjointify neg neg (λx, !neg_neg) (λa, !neg_neg)
  definition equiv_neg : ℤ ≃ ℤ := equiv.mk neg _

  definition iterate {A : Type} (f : A ≃ A) (a : ℤ) : A ≃ A :=
  rec_nat_on a erfl
               (λb g, f ⬝e g)
               (λb g, g ⬝e f⁻¹e)

  -- definition iterate_trans {A : Type} (f : A ≃ A) (a : ℤ)
  --   : iterate f a ⬝e f = iterate f (a + 1) :=
  -- sorry

  -- definition trans_iterate {A : Type} (f : A ≃ A) (a : ℤ)
  --   : f ⬝e iterate f a = iterate f (a + 1) :=
  -- sorry

  -- definition iterate_trans_symm {A : Type} (f : A ≃ A) (a : ℤ)
  --   : iterate f a ⬝e f⁻¹e = iterate f (a - 1) :=
  -- sorry

  -- definition symm_trans_iterate {A : Type} (f : A ≃ A) (a : ℤ)
  --   : f⁻¹e ⬝e iterate f a = iterate f (a - 1) :=
  -- sorry

  -- definition iterate_neg {A : Type} (f : A ≃ A) (a : ℤ)
  --   : iterate f (-a) = (iterate f a)⁻¹e :=
  -- rec_nat_on a idp
  --   (λn p, calc
  --     iterate f (-succ n) = iterate f (-n) ⬝e f⁻¹e : rec_nat_on_neg
  --       ... = (iterate f n)⁻¹e ⬝e f⁻¹e : by rewrite p
  --       ... = (f ⬝e iterate f n)⁻¹e : sorry
  --       ... = (iterate f (succ n))⁻¹e : idp)
  --   sorry

  -- definition iterate_add {A : Type} (f : A ≃ A) (a b : ℤ)
  --   : iterate f (a + b) = equiv.trans (iterate f a) (iterate f b) :=
  -- sorry

  -- definition iterate_sub {A : Type} (f : A ≃ A) (a b : ℤ)
  --   : iterate f (a - b) = equiv.trans (iterate f a) (equiv.symm (iterate f b)) :=
  -- sorry

  -- definition iterate_mul {A : Type} (f : A ≃ A) (a b : ℤ)
  --   : iterate f (a * b) = iterate (iterate f a) b :=
  -- sorry

end int open int



namespace eq
  variables {A : Type} {a : A} (p : a = a) (b : ℤ) (n : ℕ)
  definition power : a = a :=
  rec_nat_on b idp
               (λc q, q ⬝ p)
               (λc q, q ⬝ p⁻¹)
  --iterate (equiv_eq_closed_right p a) b idp

  -- definition power_neg_succ (n : ℕ) : power p (-succ n) = power p (-n) ⬝ p⁻¹ :=
  -- !rec_nat_on_neg


  set_option pp.coercions true
  -- attribute nat.add int.add int.of_num nat.of_num int.succ [constructor]
  attribute rec_nat_on [unfold-c 2]

  definition power_con : power p b ⬝ p = power p (succ b) :=
  rec_nat_on b
    idp
    (λn IH, idp)
    (λn IH, calc
      power p (-succ n) ⬝ p = (power p (-n) ⬝ p⁻¹) ⬝ p : by rewrite [↑power,rec_nat_on_neg]
        ... = power p (-n) : inv_con_cancel_right
        ... = power p (succ (-succ n)) : {(succ_neg_succ n)⁻¹})

  -- definition con_power : p ⬝ power p b = power p (succ b) :=
  -- rec_nat_on b
  --   (by rewrite ↑[power];exact !idp_con⁻¹)
  --   (λn IH, calc
  --     p ⬝ power p (succ n) = (p ⬝ power p n) ⬝ p : con.assoc
  --       ... = power p (succ (succ n)) : by rewrite IH)
  --   (λn IH, calc
  --     p ⬝ power p (-succ n) = p ⬝ (power p (-n) ⬝ p⁻¹) : by rewrite [↑power,rec_nat_on_neg]
  --       ... = (p ⬝ power p (-n)) ⬝ p⁻¹ : con.assoc
  --       ... = power p (succ (-n)) ⬝ p⁻¹ : by rewrite IH
  --       ... = power p (-pred n) ⬝ p⁻¹ : {(neg_pred n)⁻¹}
  --       ... = power p (-succ (pred n)) : sorry
  --       ... = power p (succ (-succ n)) : sorry)

  definition power_con_inv : power p b ⬝ p⁻¹ = power p (pred b) :=
  rec_nat_on b
    idp
    (λn IH, calc
      power p (succ n) ⬝ p⁻¹ = power p n : con_inv_cancel_right
        ... = power p (pred (succ n)) : by rewrite pred_nat_succ)
    (λn IH, calc
      power p (-succ n) ⬝ p⁻¹ = power p (-succ (succ n)) : by rewrite [↑power,-rec_nat_on_neg]
        ... = power p (pred (-succ n)) : by rewrite -neg_succ)

  -- definition inv_con_power : p⁻¹ ⬝ power p b = power p (pred b) :=
  -- rec_nat_on b sorry
  --              sorry
  --              sorry

end eq
