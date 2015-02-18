/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.field
Authors: Robert Lewis

Structures with multiplicative and additive components, including semirings, rings, and fields.
The development is modeled after Isabelle's library.
-/

import logic.eq logic.connectives data.unit data.sigma data.prod
import algebra.function algebra.binary algebra.group algebra.ring
open eq eq.ops

namespace algebra

variable {A : Type}

structure division_ring [class] (A : Type) extends ring A, has_inv A :=
  (mul_inv_cancel : ∀{a}, a ≠ zero → mul a (inv a) = one)
  (inv_mul_cancel : ∀{a}, a ≠ zero → mul (inv a) a = one)

-- theorem div_is_mul [s : division_ring A] {a b : A} : a / b = a * b⁻¹ := rfl

section division_ring
  variables [s : division_ring A] {a b c : A}
  include s

  definition divide (a b : A) : A := a * b⁻¹
  infix `/` := divide

  theorem mul_inv_cancel (H : a ≠ 0) : a * a⁻¹ = 1 :=
  division_ring.mul_inv_cancel H

  theorem inv_mul_cancel (H : a ≠ 0) : a⁻¹ * a = 1 :=
  division_ring.inv_mul_cancel H

  theorem inv_eq_one_div (H : a ≠ 0) : a⁻¹ = 1 / a := 
    symm (calc
      1 / a = 1 * a⁻¹ : rfl --div_is_mul _ _ H
      ... = a⁻¹ : one_mul
      )

  theorem mul_one_div_cancel (H : a ≠ 0) : a * (1 / a) = 1 :=
    calc
      a * (1 / a) = a * a⁻¹ : inv_eq_one_div H
      ... = 1 : mul_inv_cancel H

  theorem one_div_mul_cancel (H : a ≠ 0) : (1 / a) * a = 1 :=
    calc
      (1 / a) * a = a⁻¹ * a : inv_eq_one_div H
      ... = 1 : inv_mul_cancel H

  theorem div_self (H : a ≠ 0) : a / a = 1 :=
    calc
      a / a = a * a⁻¹ : rfl
      ... = 1 : mul_inv_cancel H

  theorem mul_div_assoc (Hc : c ≠ 0) : (a * b) / c = a * (b / c) :=
    eq.symm (calc
      a * (b / c) = a * (b * c⁻¹) : rfl
      ... = (a * b) * c⁻¹ : mul.assoc
      ... = (a * b) / c : rfl)

  theorem one_div_ne_zero (H : a ≠ 0) : 1 / a ≠ 0 :=
    assume H2 : 1 / a = 0,
    have C1 : 0 = 1, from symm (calc
      1 = a * (1 / a) : mul_one_div_cancel H
      ... = a * 0 : H2
      ... = 0 : mul_zero),
      absurd C1 zero_ne_one

  -- the analogue in group is called inv_one
  theorem inv_one_is_one : 1⁻¹ = 1 :=
  calc
    1⁻¹ = 1⁻¹ * 1 : mul_one
     ... = 1      : inv_mul_cancel (ne.symm zero_ne_one)

  theorem div_one : a / 1 = a :=
    calc
      a / 1 = a * 1⁻¹ : rfl
      ... = a * 1 : inv_one_is_one
      ... = a : mul_one

  -- note: integral domain has a "mul_ne_zero". When we get to "field", show it is an
  -- instance of an integral domain, so we can use that theorem.
  -- check @mul_ne_zero
  theorem mul_ne_zero' (Ha : a ≠ 0) (Hb : b ≠ 0) : a * b ≠ 0 :=
    assume H : a * b = 0,
    have C1 : a = 0, from (calc
      a = a * 1 : mul_one
      ... = a * (b * (1 / b)) : mul_one_div_cancel Hb
      ... = (a * b) * (1 / b) : mul.assoc
      ... = 0 * (1 / b) : H
      ... = 0 : zero_mul),
      absurd C1 Ha

  theorem mul_ne_zero_imp_ne_zero (H : a * b ≠ 0) : a ≠ 0 ∧ b ≠ 0 :=
    have Ha : a ≠ 0, from
      (assume Ha1 : a = 0,
        have H1 : a * b = 0, from (calc
          a * b = 0 * b : Ha1
          ... = 0 : zero_mul),
        absurd H1 H),
    have Hb : b ≠ 0, from
      (assume Hb1 : b = 0,
        have H1 : a * b = 0, from (calc
          a * b = a * 0 : Hb1
          ... = 0 : mul_zero),
        absurd H1 H),
    and.intro Ha Hb

  theorem mul_ne_zero_comm (H : a * b ≠ 0) : b * a ≠ 0 :=
    have H2 : a ≠ 0 ∧ b ≠ 0, from mul_ne_zero_imp_ne_zero H,
    mul_ne_zero' (and.right H2) (and.left H2)

--  theorem inv_zero_imp_zero (H : a⁻¹ = 0) : a = 0 :=
-- classical?

  -- make "left" and "right" versions?
  theorem eq_one_div_of_mul_eq_one (H : a * b = 1) : b = 1 / a :=
    have H2 : a ≠ 0, from 
      (assume A : a = 0,
      have B : 0 = 1, from symm (calc
        1 = a * b : symm H
      ... = 0 * b : A
      ... = 0 : zero_mul),
      absurd B zero_ne_one),
    show b = 1 / a, from symm (calc
      1 / a = (1 / a) * 1 : mul_one
      ... = (1 / a) * (a * b) : H
      ... = (1 / a) * a * b : mul.assoc
      ... = 1 * b : one_div_mul_cancel H2
      ... = b : one_mul)

  -- which one is left and which is right?
  theorem eq_one_div_of_mul_eq_one_left (H : b * a = 1) : b = 1 / a :=
    have H2 : a ≠ 0, from 
      (assume A : a = 0,
      have B : 0 = 1, from symm (calc
        1 = b * a : symm H
      ... = b * 0 : A
      ... = 0 : mul_zero),
      absurd B zero_ne_one),
    show b = 1 / a, from symm (calc
      1 / a = 1 * (1 / a) : one_mul
      ... = b * a * (1 / a) : H
      ... = b * (a * (1 / a)) : mul.assoc
      ... = b * 1 : mul_one_div_cancel H2
      ... = b : mul_one)

  theorem one_div_mul_one_div (Ha : a ≠ 0) (Hb : b ≠ 0) : (1 / a) * (1 / b) = 1 / (b * a) :=
    have H : (b * a) * ((1 / a) * (1 / b)) = 1, from (calc
      (b * a) * ((1 / a) * (1 / b)) = b * (a * ((1 / a) * (1 / b))) : mul.assoc
      ... = b * ((a * (1 / a)) * (1 / b)) : mul.assoc
      ... = b * (1 * (1 / b)) : mul_one_div_cancel Ha
      ... = b * (1 / b) : one_mul
      ... = 1 : mul_one_div_cancel Hb),
    eq_one_div_of_mul_eq_one H 

  theorem one_div_neg_one_eq_neg_one : 1 / (-1) = -1 :=
    have H : (-1) * (-1) = 1, from calc
      (-1) * (-1) = - (-1) : neg_eq_neg_one_mul
      ... = 1 : neg_neg,
    symm (eq_one_div_of_mul_eq_one H)

  -- this should be in ring
  theorem mul_neg_one_eq_neg : a * (-1) = -a :=
    have H : a + a * -1 = 0, from calc
      a + a * -1 = a * 1 + a * -1 : mul_one
      ... = a * (1 + -1) : left_distrib
      ... = a * 0 : add.right_inv
      ... = 0 : mul_zero,
    symm (neg_eq_of_add_eq_zero H)

  theorem one_div_neg_eq_neg_one_div (H : a ≠ 0) : 1 / (- a) = - (1 / a) := 
    have H1 : -1 ≠ 0, from
      (assume H2 : -1 = 0, absurd (symm (calc
        1 = -(-1) : neg_neg
        ... = -0 : H2
        ... = 0 : neg_zero)) zero_ne_one),
    calc
      1 / (- a) = 1 / ((-1) * a) : neg_eq_neg_one_mul
      ... = (1 / a) * (1 / (- 1)) : one_div_mul_one_div H H1 
      ... = (1 / a) * (-1) : one_div_neg_one_eq_neg_one
      ... = - (1 / a) : mul_neg_one_eq_neg

  theorem div_div (H : a ≠ 0) : 1 / (1 / a) = a :=
    symm (eq_one_div_of_mul_eq_one_left (mul_one_div_cancel H))

  theorem eq_of_invs_eq (Ha : a ≠ 0) (Hb : b ≠ 0) (H : 1 / a = 1 / b) : a = b :=
    calc
      a = 1 / (1 / a) : div_div Ha
      ... = 1 / (1 / b) : H
      ... = b : div_div Hb

  -- oops, the analogous theorem in group is called inv_mul, but it *should* be called
  -- mul_inv, in which case, we will have to rename this one
  theorem mul_inv (Ha : a ≠ 0) (Hb : b ≠ 0) : (b * a)⁻¹ = a⁻¹ * b⁻¹ :=
    have H1 : b * a ≠ 0, from mul_ne_zero' Hb Ha,
    eq.symm (calc
      a⁻¹ * b⁻¹ = (1 / a) * b⁻¹ : inv_eq_one_div Ha
      ... = (1 / a) * (1 / b) : inv_eq_one_div Hb
      ... = (1 / (b * a)) : one_div_mul_one_div Ha Hb
      ... = (b * a)⁻¹ : inv_eq_one_div H1)

  theorem mul_div_cancel (Hb : b ≠ 0) : a * b / b = a :=
    calc
      (a * b) / b = a * b * b⁻¹ : rfl
      ... = a * (b * b⁻¹) : mul.assoc
      ... = a * 1 : mul_inv_cancel Hb
      ... = a : mul_one

  theorem div_mul_cancel (Hb : b ≠ 0) : a / b * b = a :=
    calc
      (a / b) * b = (a * b⁻¹) * b : rfl
      ... = a * (b⁻¹ * b) : mul.assoc
      ... = a * 1 : inv_mul_cancel Hb
      ... = a : mul_one

  theorem div_add_div_same (Hc : c ≠ 0) : a / c + b / c = (a + b) / c :=
    calc
      (a / c) + (b / c) = (a * c⁻¹) + (b / c) : rfl
      ... = a * c⁻¹ + b * c⁻¹ : rfl
      ... = (a + b) * c⁻¹ : right_distrib
      ... = (a + b) / c : rfl

end division_ring

structure field [class] (A : Type) extends  division_ring A, comm_ring A

section field
  variables [s : field A] {a b c d: A}
  include s

  -- I think of "div_cancel" has being something like a * b / b = a or a / b * b = a. The name
  -- I chose is clunky, but it has the right prefix
  theorem div_mul_self_left (Hb : b ≠ 0) (H : a * b ≠ 0) : a / (a * b) = 1 / b :=
    have Ha : a ≠ 0, from and.left (mul_ne_zero_imp_ne_zero H),
    symm (calc
      1 / b = 1 * (1 / b) : one_mul
      ... = (a * a⁻¹) * (1 / b) : mul_inv_cancel Ha
      ... = a * (a⁻¹ * (1 / b)) : mul.assoc
      ... = a * ((1 / a) * (1 / b)) :inv_eq_one_div Ha
      ... = a * (1 / (b * a)) : one_div_mul_one_div Ha Hb
      ... = a * (1 / (a * b)) : mul.comm
      ... = a * (a * b)⁻¹ : inv_eq_one_div H
      ... = a / (a * b) : rfl)

  theorem div_mul_self_right (Ha : a ≠ 0) (H : a * b ≠ 0) : b / (a * b) = 1 / a :=
    have H1 : b * a ≠ 0, from mul_ne_zero_comm H,
    calc
      (b / (a * b)) = (b / (b * a)) : mul.comm
      ... = 1 / a : div_mul_self_left Ha H1

  theorem mul_div_cancel_left (Ha : a ≠ 0) : a * b / a = b :=
    calc
      (a * b) / a = (b * a) / a : mul.comm
      ... = b : mul_div_cancel Ha

  theorem mul_div_cancel' (Hb : b ≠ 0) : b * (a / b) = a :=
    calc
      b * (a / b) = a / b * b : mul.comm
      ... = a : div_mul_cancel Hb

  theorem one_div_add_one_div (Ha : a ≠ 0) (Hb : b ≠ 0) : 1 / a + 1 / b = (a + b) / (a * b) :=
    have H : a * b ≠ 0, from (mul_ne_zero' Ha Hb),
    symm (calc
      (a + b) / (a * b) = (a + b) * (a * b)⁻¹ : rfl
      ... = a * (a * b)⁻¹ + b * (a * b)⁻¹ : right_distrib
      ... = a / (a * b) + b * (a * b)⁻¹ : rfl
      ... = 1 / b + b * (a * b)⁻¹ : div_mul_self_left Hb H
      ... = 1 / b + b / (a * b) : rfl
      ... = 1 / b + 1 / a : div_mul_self_right Ha H
      ... = 1 / a + 1 / b : add.comm)

  theorem div_mul_div (Hb : b ≠ 0) (Hd : d ≠ 0) : (a / b) * (c / d) = (a * c) / (b * d) :=
    calc
      (a / b) * (c / d) = (a * b⁻¹) * (c / d) : rfl
      ... = (a * b⁻¹) * (c * d⁻¹) : rfl
      ... = (a * c) * (d⁻¹ * b⁻¹) : by rewrite [2 mul.assoc, (mul.comm b⁻¹), mul.assoc]
      ... = (a * c) * (b * d)⁻¹ : mul_inv Hd Hb
      ... = (a * c) / (b * d) : rfl

  theorem mul_div_mul_left (Hb : b ≠ 0) (Hc : c ≠ 0) : (c * a) / (c * b) = a / b :=
    have H : c * b ≠ 0, from mul_ne_zero' Hc Hb,
    calc
      (c * a) / (c * b) = (c / c) * (a / b) : div_mul_div Hc Hb
      ... = 1 * (a / b) : div_self Hc
      ... = a / b : one_mul

  theorem mul_div_mul_right (Hb : b ≠ 0) (Hc : c ≠ 0) : (a * c) / (b * c) = a / b :=
    calc
      (a * c) / (b * c) = (c * a) / (b * c) : mul.comm
      ... = (c * a) / (c * b) : mul.comm
      ... = a / b : mul_div_mul_left Hb Hc

  theorem div_mul_eq_mul_div (Hc : c ≠ 0) : (b / c) * a = (b * a) / c :=
    calc
      (b / c) * a = (b * c⁻¹) * a : rfl
      ... = (b * a) * c⁻¹ : by rewrite [mul.assoc, (mul.comm c⁻¹), -mul.assoc ]
      ... = (b * a) / c : rfl

  -- this one is odd -- I am not sure what to call it, but again, the prefix is right
  theorem div_mul_eq_mul_div_comm (Hc : c ≠ 0) : (b / c) * a = b * (a / c) :=
    calc
      (b / c) * a = (b * a) / c : div_mul_eq_mul_div Hc
      ... = (b * a) / (1 * c) : one_mul
      ... = (b / 1) * (a / c) : div_mul_div (ne.symm zero_ne_one) Hc
      ... = b * (a / c) : div_one

  theorem div_add_div (Hb : b ≠ 0) (Hd : d ≠ 0) :
      (a / b) + (c / d) = ((a * d) + (b * c)) / (b * d) :=
    have H : b * d ≠ 0, from mul_ne_zero' Hb Hd,
    calc
      a / b + c / d = (a * d) / (b * d) + c / d : mul_div_mul_right Hb Hd
      ... = (a * d) / (b * d) + (b * c) / (b * d) : mul_div_mul_left Hd Hb
      ... = ((a * d) + (b * c)) / (b * d) : div_add_div_same H


  theorem div_sub_div (Hb : b ≠ 0) (Hd : d ≠ 0) :
      (a / b) - (c / d) = ((a * d) - (b * c)) / (b * d) :=
    calc
      (a / b) - (c / d) = (a / b) + -1 * (c / d) : neg_eq_neg_one_mul
      ... = (a / b) + ((-1 * c) / d) : mul_div_assoc Hd
      ... = ((a * d) + (b * (-1 * c))) / (b * d) : div_add_div Hb Hd
      ... = ((a * d) + -1 * (b * c)) / (b * d) : by rewrite [-mul.assoc, (mul.comm b), mul.assoc]
      ... = ((a * d) + -(b * c)) / (b * d) : neg_eq_neg_one_mul

   
  theorem mul_eq_mul_of_div_eq_div (Hb : b ≠ 0) (Hd : d ≠ 0) (H : a / b = c / d) : a * d = c * b :=
    calc
      a * d = a * 1 * d : by rewrite [-mul_one, mul.assoc, (mul.comm d), -mul.assoc]
      ... = (a * (b / b)) * d : div_self Hb
      ... = ((a / b) * b) * d : div_mul_eq_mul_div_comm Hb
      ... = ((c / d) * b) * d : H
      ... = ((c * b) / d) * d : div_mul_eq_mul_div Hd
      ... = c * b : div_mul_cancel Hd

end field

end algebra
