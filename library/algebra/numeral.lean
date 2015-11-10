/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/

import algebra.ordered_field
open algebra

namespace norm_num

variable {A : Type}

definition add1 [s : has_add A] [s' : has_one A] (a : A) : A := add a one

theorem add_comm_four [s : add_comm_semigroup A] (a b : A) : a + a + (b + b) = (a + b) + (a + b) :=
  by rewrite [-add.assoc at {1}, add.comm, {a + b}add.comm at {1}, *add.assoc]

theorem add_comm_middle [s : add_comm_semigroup A] (a b c : A) : a + b + c = a + c + b :=
  by rewrite [add.assoc, add.comm b, -add.assoc]

theorem bit0_add_bit0 [s : add_comm_semigroup A] (a b : A) : bit0 a + bit0 b = bit0 (a + b) :=
  !add_comm_four

theorem bit0_add_bit0_helper [s : add_comm_semigroup A] (a b t : A) (H : a + b = t) :
        bit0 a + bit0 b = bit0 t :=
  by rewrite -H; apply bit0_add_bit0

theorem bit1_add_bit0 [s : add_comm_semigroup A] [s' : has_one A] (a b : A) :
        bit1 a + bit0 b = bit1 (a + b) :=
  begin
    rewrite [↑bit0, ↑bit1, add_comm_middle], congruence, apply add_comm_four
  end

theorem bit1_add_bit0_helper [s : add_comm_semigroup A] [s' : has_one A] (a b t : A)
        (H : a + b = t) : bit1 a + bit0 b = bit1 t :=
  by rewrite -H; apply bit1_add_bit0

theorem bit0_add_bit1 [s : add_comm_semigroup A] [s' : has_one A] (a b : A) :
        bit0 a + bit1 b = bit1 (a + b) :=
  by rewrite [{bit0 a + _}add.comm, {a + _}add.comm]; apply bit1_add_bit0

theorem bit0_add_bit1_helper [s : add_comm_semigroup A] [s' : has_one A] (a b t : A)
        (H : a + b = t) : bit0 a + bit1 b = bit1 t :=
  by rewrite -H; apply bit0_add_bit1

theorem bit1_add_bit1 [s : add_comm_semigroup A] [s' : has_one A] (a b : A) :
        bit1 a + bit1 b = bit0 (add1 (a + b)) :=
  begin
    rewrite ↑[bit0, bit1, add1, add.assoc],
    rewrite [*add.assoc, {_ + (b + 1)}add.comm, {_ + (b + 1 + _)}add.comm,
      {_ + (b + 1 + _ + _)}add.comm, *add.assoc, {1 + a}add.comm, -{b + (a + 1)}add.assoc,
      {b + a}add.comm, *add.assoc]
  end

theorem bit1_add_bit1_helper [s : add_comm_semigroup A] [s' : has_one A] (a b t s: A)
        (H : (a + b) = t) (H2 : add1 t = s) : bit1 a + bit1 b = bit0 s :=
  begin rewrite [-H2, -H], apply bit1_add_bit1 end

theorem bin_add_zero [s : add_monoid A] (a : A) : a + zero = a := !add_zero

theorem bin_zero_add [s : add_monoid A] (a : A) : zero + a = a := !zero_add

theorem one_add_bit0 [s : add_comm_semigroup A] [s' : has_one A] (a : A) : one + bit0 a = bit1 a :=
  begin rewrite ↑[bit0, bit1], rewrite add.comm end

theorem bit0_add_one [s : has_add A] [s' : has_one A] (a : A) : bit0 a + one = bit1 a :=
  rfl

theorem bit1_add_one [s : has_add A] [s' : has_one A] (a : A) : bit1 a + one = add1 (bit1 a) :=
  rfl

theorem bit1_add_one_helper [s : has_add A] [s' : has_one A] (a t : A) (H : add1 (bit1 a) = t) :
        bit1 a + one = t :=
  by rewrite -H

theorem one_add_bit1 [s : add_comm_semigroup A] [s' : has_one A] (a : A) :
        one + bit1 a = add1 (bit1 a) := !add.comm

theorem one_add_bit1_helper [s : add_comm_semigroup A] [s' : has_one A] (a t : A)
        (H : add1 (bit1 a) = t) : one + bit1 a = t :=
  by rewrite -H; apply one_add_bit1

theorem add1_bit0 [s : has_add A] [s' : has_one A] (a : A) : add1 (bit0 a) = bit1 a :=
  rfl

theorem add1_bit1 [s : add_comm_semigroup A] [s' : has_one A] (a : A) :
        add1 (bit1 a) = bit0 (add1 a) :=
  begin
    rewrite ↑[add1, bit1, bit0],
    rewrite [add.assoc, add_comm_four]
  end

theorem add1_bit1_helper [s : add_comm_semigroup A] [s' : has_one A] (a t : A) (H : add1 a = t) :
        add1 (bit1 a) = bit0 t :=
  by rewrite -H; apply add1_bit1

theorem add1_one [s : has_add A] [s' : has_one A] : add1 (one : A) = bit0 one :=
  rfl

theorem add1_zero [s : add_monoid A] [s' : has_one A] : add1 (zero : A) = one :=
  begin
    rewrite [↑add1, zero_add]
  end

theorem one_add_one [s : has_add A] [s' : has_one A] : (one : A) + one = bit0 one :=
  rfl

theorem subst_into_sum [s : has_add A] (l r tl tr t : A) (prl : l = tl) (prr : r = tr)
        (prt : tl + tr = t) : l + r = t :=
   by rewrite [prl, prr, prt]

-- multiplication

theorem mul_zero [s : mul_zero_class A] (a : A) : a * zero = zero :=
  by rewrite [↑zero, mul_zero]

theorem zero_mul [s : mul_zero_class A] (a : A) : zero * a = zero :=
  by rewrite [↑zero, zero_mul]

theorem mul_one [s : monoid A] (a : A) : a * one = a :=
  by rewrite [↑one, mul_one]

theorem mul_bit0 [s : distrib A] (a b : A) : a * (bit0 b) = bit0 (a * b) :=
  by rewrite [↑bit0, left_distrib]

theorem mul_bit0_helper [s : distrib A] (a b t : A) (H : a * b = t) : a * (bit0 b) = bit0 t :=
  by rewrite -H; apply mul_bit0

theorem mul_bit1 [s : semiring A] (a b : A) : a * (bit1 b) = bit0 (a * b) + a :=
  by rewrite [↑bit1, ↑bit0, +left_distrib, ↑one, mul_one]

theorem mul_bit1_helper [s : semiring A] (a b s t : A) (Hs : a * b = s) (Ht : bit0 s + a  = t) :
        a * (bit1 b) = t :=
  begin rewrite [-Ht, -Hs, mul_bit1] end

theorem subst_into_prod [s : has_mul A] (l r tl tr t : A) (prl : l = tl) (prr : r = tr)
        (prt : tl * tr = t) :
        l * r = t :=
   by rewrite [prl, prr, prt]

theorem mk_cong (op : A → A) (a b : A) (H : a = b) : op a = op b :=
  by congruence; exact H

theorem mk_eq (a : A) : a = a := rfl

theorem neg_add_neg_eq_of_add_add_eq_zero [s : add_comm_group A] (a b c : A) (H : c + a + b = 0) :
        -a + -b = c :=
  begin
    apply add_neg_eq_of_eq_add,
    apply neg_eq_of_add_eq_zero,
    rewrite [add.comm, add.assoc, add.comm b, -add.assoc, H]
  end

theorem neg_add_neg_helper [s : add_comm_group A] (a b c : A) (H : a + b = c) : -a + -b = -c :=
  begin apply iff.mp !neg_eq_neg_iff_eq, rewrite [neg_add, *neg_neg, H] end

theorem neg_add_pos_eq_of_eq_add [s : add_comm_group A] (a b c : A) (H : b = c + a) : -a + b = c :=
  begin apply neg_add_eq_of_eq_add, rewrite add.comm, exact H end

theorem neg_add_pos_helper1 [s : add_comm_group A] (a b c : A) (H : b + c = a) : -a + b = -c :=
  begin apply neg_add_eq_of_eq_add, apply eq_add_neg_of_add_eq H end

theorem neg_add_pos_helper2 [s : add_comm_group A] (a b c : A) (H : a + c = b) : -a + b = c :=
  begin apply neg_add_eq_of_eq_add, rewrite H end

theorem pos_add_neg_helper [s : add_comm_group A] (a b c : A) (H : b + a = c) : a + b = c :=
  by rewrite [add.comm, H]

theorem sub_eq_add_neg_helper [s : add_comm_group A] (t₁ t₂ e w₁ w₂: A) (H₁ : t₁ = w₁)
        (H₂ : t₂ = w₂) (H : w₁ + -w₂ = e) : t₁ - t₂ = e :=
  by rewrite [sub_eq_add_neg, H₁, H₂, H]

theorem pos_add_pos_helper [s : add_comm_group A] (a b c h₁ h₂ : A) (H₁ : a = h₁) (H₂ : b = h₂)
        (H : h₁ + h₂ = c) : a + b = c :=
  by rewrite [H₁, H₂, H]

theorem subst_into_subtr [s : add_group A] (l r t : A) (prt : l + -r = t) : l - r = t :=
   by rewrite [sub_eq_add_neg, prt]

theorem neg_neg_helper [s : add_group A] (a b : A) (H : a = -b) : -a = b :=
  by rewrite [H, neg_neg]

theorem neg_mul_neg_helper [s : ring A] (a b c : A) (H : a * b = c) : (-a) * (-b) = c :=
  begin rewrite [neg_mul_neg, H] end

theorem neg_mul_pos_helper [s : ring A] (a b c : A) (H : a * b = c) : (-a) * b = -c :=
  begin rewrite [-neg_mul_eq_neg_mul, H] end

theorem pos_mul_neg_helper [s : ring A] (a b c : A) (H : a * b = c) : a * (-b) = -c :=
  begin rewrite [-neg_mul_comm, -neg_mul_eq_neg_mul, H] end

theorem pos_bit0_helper [s : linear_ordered_semiring A] (a : A) (H : a > 0) : bit0 a > 0 :=
  by rewrite ↑bit0; apply add_pos H H

theorem nonneg_bit0_helper [s : linear_ordered_semiring A] (a : A) (H : a ≥ 0) : bit0 a ≥ 0 :=
  by rewrite ↑bit0; apply add_nonneg H H

theorem pos_bit1_helper [s : linear_ordered_semiring A] (a : A) (H : a ≥ 0) : bit1 a > 0 :=
  begin
    rewrite ↑bit1,
    apply add_pos_of_nonneg_of_pos,
    apply nonneg_bit0_helper _ H,
    apply zero_lt_one
  end

theorem nonneg_bit1_helper [s : linear_ordered_semiring A] (a : A) (H : a ≥ 0) : bit1 a ≥ 0 :=
  by apply le_of_lt; apply pos_bit1_helper _ H

theorem div_add_helper [s : field A] (n d b c val : A) (Hd : d ≠ 0) (H : n + b * d = val)
        (H2 : c * d = val) : n / d + b = c :=
  begin
    apply eq_of_mul_eq_mul_of_nonzero_right Hd,
    rewrite [H2, -H, right_distrib, div_mul_cancel _ Hd]
 end

theorem add_div_helper [s : field A] (n d b c val : A) (Hd : d ≠ 0) (H : d * b + n = val)
        (H2 : d * c = val) : b + n / d = c :=
  begin
    apply eq_of_mul_eq_mul_of_nonzero_left Hd,
    rewrite [H2, -H, left_distrib, mul_div_cancel' Hd]
 end

theorem div_mul_helper [s : field A] (n d c v : A) (Hd : d ≠ 0) (H : (n * c) / d = v) :
        (n / d) * c = v :=
  by rewrite [-H, field.div_mul_eq_mul_div_comm _ _ Hd, mul_div_assoc]

theorem mul_div_helper [s : field A] (a n d v : A) (Hd : d ≠ 0) (H : (a * n) / d = v) :
        a * (n / d) = v :=
  by rewrite [-H, mul_div_assoc]

theorem nonzero_of_pos_helper [s : linear_ordered_semiring A] (a : A) (H : a > 0) : a ≠ 0 :=
  ne_of_gt H

theorem nonzero_of_neg_helper [s : linear_ordered_ring A] (a : A) (H : a ≠ 0) : -a ≠ 0 :=
  begin intro Ha, apply H, apply eq_of_neg_eq_neg, rewrite neg_zero, exact Ha end

theorem nonzero_of_div_helper [s : field A] (a b : A) (Ha : a ≠ 0) (Hb : b ≠ 0) : a / b ≠ 0 :=
  begin
    intro Hab,
    have Habb : (a / b) * b = 0, by rewrite [Hab, zero_mul],
    rewrite [div_mul_cancel _ Hb at Habb],
    exact Ha Habb
  end

theorem div_helper [s : field A] (n d v : A) (Hd : d ≠ 0) (H : v * d = n) : n / d = v :=
  begin
    apply eq_of_mul_eq_mul_of_nonzero_right Hd,
    rewrite (div_mul_cancel _ Hd),
    exact eq.symm H
  end

theorem div_eq_div_helper [s : field A] (a b c d v : A) (H1 : a * d = v) (H2 : c * b = v)
        (Hb : b ≠ 0) (Hd : d ≠ 0) : a / b = c / d :=
  begin
    apply eq_div_of_mul_eq,
    exact Hd,
    rewrite div_mul_eq_mul_div,
    apply eq.symm,
    apply eq_div_of_mul_eq,
    exact Hb,
    rewrite [H1, H2]
  end

theorem subst_into_div [s : has_div A] (a₁ b₁ a₂ b₂ v : A) (H : a₁ / b₁ = v) (H1 : a₂ = a₁)
        (H2 : b₂ = b₁) : a₂ / b₂ = v :=
  by rewrite [H1, H2, H]

theorem neg_zero_helper [s : add_group A] (a : A) (H : a = 0) : - a = 0 :=
  by rewrite [H, neg_zero]

end norm_num
