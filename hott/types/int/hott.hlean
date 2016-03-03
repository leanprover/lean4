/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Theorems about the integers specific to HoTT
-/

import .basic types.eq arity algebra.bundled
open core eq is_equiv equiv algebra is_trunc
open nat (hiding pred)

namespace int

  section
  open algebra
  definition group_integers : Group :=
  Group.mk ℤ (group_of_add_group _)
  end

  definition is_equiv_succ [instance] : is_equiv succ :=
  adjointify succ pred (λa, !add_sub_cancel) (λa, !sub_add_cancel)
  definition equiv_succ : ℤ ≃ ℤ := equiv.mk succ _

  definition is_equiv_neg [instance] : is_equiv (neg : ℤ → ℤ) :=
  adjointify neg neg (λx, !neg_neg) (λa, !neg_neg)
  definition equiv_neg : ℤ ≃ ℤ := equiv.mk neg _

  definition iterate {A : Type} (f : A ≃ A) (a : ℤ) : A ≃ A :=
  rec_nat_on a erfl
               (λb g, f ⬝e g)
               (λb g, g ⬝e f⁻¹ᵉ)

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
  variables {A : Type} {a : A} (p : a = a) (b c : ℤ) (n : ℕ)
  definition power : a = a :=
  rec_nat_on b idp
               (λc q, q ⬝ p)
               (λc q, q ⬝ p⁻¹)
  --iterate (equiv_eq_closed_right p a) b idp

  -- definition power_neg_succ (n : ℕ) : power p (-succ n) = power p (-n) ⬝ p⁻¹ :=
  -- !rec_nat_on_neg

  -- local attribute nat.add int.add int.of_num nat.of_num int.succ [constructor]

  definition power_con : power p b ⬝ p = power p (succ b) :=
  rec_nat_on b
    idp
    (λn IH, idp)
    (λn IH, calc
      power p (-succ n) ⬝ p
            = (power p (-int.of_nat n) ⬝ p⁻¹) ⬝ p : by rewrite [↑power,-rec_nat_on_neg]
        ... = power p (-int.of_nat n) : inv_con_cancel_right
        ... = power p (succ (-succ n)) : by rewrite -succ_neg_succ)

  definition power_con_inv : power p b ⬝ p⁻¹ = power p (pred b) :=
  rec_nat_on b
    idp
    (λn IH, calc
      power p (succ n) ⬝ p⁻¹ = power p n : by apply con_inv_cancel_right
        ... = power p (pred (succ n))   : by rewrite pred_nat_succ)
    (λn IH, calc
      power p (-int.of_nat (succ n)) ⬝ p⁻¹
            = power p (-int.of_nat (succ (succ n))) : by rewrite [↑power,-rec_nat_on_neg]
        ... = power p (pred (-succ n)) : by rewrite -neg_succ)

  definition con_power : p ⬝ power p b = power p (succ b) :=
  rec_nat_on b
  ( by rewrite ↑[power];exact !idp_con⁻¹)
  ( λn IH, proof calc
    p ⬝ power p (succ n) = (p ⬝ power p n) ⬝ p : con.assoc p _ p
      ... = power p (succ (succ n)) : by rewrite IH qed)
  ( λn IH, calc
          p ⬝ power p (-int.of_nat (succ n))
                = p ⬝ (power p (-int.of_nat n) ⬝ p⁻¹) : by rewrite [↑power, rec_nat_on_neg]
            ... = (p ⬝ power p (-int.of_nat n)) ⬝ p⁻¹ : con.assoc
            ... = power p (succ (-int.of_nat n)) ⬝ p⁻¹ : by rewrite IH
            ... = power p (pred (succ (-int.of_nat n))) : power_con_inv
            ... = power p (succ (-int.of_nat (succ n))) : by rewrite [succ_neg_nat_succ,int.pred_succ])

  definition inv_con_power : p⁻¹ ⬝ power p b = power p (pred b) :=
  rec_nat_on b
  ( by rewrite ↑[power];exact !idp_con⁻¹)
  (λn IH, calc
    p⁻¹ ⬝ power p (succ n) = p⁻¹ ⬝ power p n ⬝ p : con.assoc
      ... = power p (pred n) ⬝ p : by rewrite IH
      ... = power p (succ (pred n)) : power_con
      ... = power p (pred (succ n)) : by rewrite [succ_pred,-int.pred_succ n])
  ( λn IH, calc
    p⁻¹ ⬝ power p (-int.of_nat (succ n))
          = p⁻¹ ⬝ (power p (-int.of_nat n) ⬝ p⁻¹) : by rewrite [↑power,rec_nat_on_neg]
      ... = (p⁻¹ ⬝ power p (-int.of_nat n)) ⬝ p⁻¹ : con.assoc
      ... = power p (pred (-int.of_nat n)) ⬝ p⁻¹ : by rewrite IH
      ... = power p (-int.of_nat (succ n)) ⬝ p⁻¹ : by rewrite -neg_succ
      ... = power p (-succ (succ n)) : by rewrite [↑power,-rec_nat_on_neg]
      ... = power p (pred (-succ n)) : by rewrite -neg_succ)

  definition power_con_power : Π(b : ℤ), power p b ⬝ power p c = power p (b + c) :=
  rec_nat_on c
    (λb, by rewrite int.add_zero)
    (λn IH b, by rewrite [-con_power,-con.assoc,power_con,IH,↑succ,add.assoc,
                          add.comm (int.of_nat n)])
    (λn IH b, by rewrite [neg_nat_succ,-inv_con_power,-con.assoc,power_con_inv,IH,↑pred,
                          +sub_eq_add_neg,add.assoc,add.comm (-n)])

end eq
