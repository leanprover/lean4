/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/

import algebra.ring
open algebra

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

theorem bit1_add_bit0_helper [s : add_comm_semigroup A] [s' : has_one A] (a b t : A) (H : a + b = t) :
        bit1 a + bit0 b = bit1 t :=
  by rewrite -H; apply bit1_add_bit0

theorem bit0_add_bit1 [s : add_comm_semigroup A] [s' : has_one A] (a b : A) :
        bit0 a + bit1 b = bit1 (a + b) :=
  by rewrite [{bit0 a + _}add.comm, {a + _}add.comm]; apply bit1_add_bit0

theorem bit0_add_bit1_helper [s : add_comm_semigroup A] [s' : has_one A] (a b t : A) (H : a + b = t) :
        bit0 a + bit1 b = bit1 t :=
  by rewrite -H; apply bit0_add_bit1

theorem bit1_add_bit1 [s : add_comm_semigroup A] [s' : has_one A] (a b : A) : bit1 a + bit1 b = bit0 (add1 (a + b)) :=
  begin
    rewrite ↑[bit0, bit1, add1],
    apply sorry
  end

theorem bit1_add_bit1_helper [s : add_comm_semigroup A] [s' : has_one A] (a b t s: A)
        (H : (a + b) = t) (H2 : add1 t = s) : bit1 a + bit1 b = bit0 s :=
  begin rewrite [-H2, -H], apply bit1_add_bit1 end

theorem bin_add_zero [s : add_monoid A] (a : A) : a + zero = a := !add_zero

theorem bin_zero_add [s : add_monoid A] (a : A) : zero + a = a := !zero_add

theorem one_add_bit0 [s : add_comm_semigroup A] [s' : has_one A] (a : A) : one + bit0 a = bit1 a :=
  begin rewrite ↑[bit0, bit1], rewrite add.comm end

theorem bit0_add_one [s : has_add A] [s' : has_one A] (a : A) : bit0 a + one = bit1 a := rfl

theorem bit1_add_one [s : has_add A] [s' : has_one A] (a : A) : bit1 a + one = add1 (bit1 a) := rfl

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

theorem subst_into_sum [s : has_add A] (l r tl tr t : A) (prl : l = tl) (prr : r = tr) (prt : tl + tr = t) :
        l + r = t :=
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

theorem neg_add_neg_eq_of_add_add_eq_zero [s : add_comm_group A] (a b c : A) (H : c + a + b = 0) : -a + -b = c :=
  begin apply add_neg_eq_of_eq_add, apply neg_eq_of_add_eq_zero, rewrite [add.comm, add.assoc, add.comm b, -add.assoc, H]  end

/-theorem neg_add_neg_helper [s : add_comm_group A] (t₁ t₂ e w₁ w₂ : A) (H₁ : t₁ = -w₁)
        (H₂ : t₂ = -w₂) (H : e + w₁ + w₂ = 0) : t₁ + t₂ = e :=
  by rewrite [H₁, H₂, neg_add_neg_eq_of_add_add_eq_zero _ _ _ H]-/

theorem neg_add_neg_helper [s : add_comm_group A] (a b c : A) (H : a + b = c) : -a + -b = -c :=
  begin apply iff.mp !neg_eq_neg_iff_eq, rewrite [neg_add, *neg_neg, H] end

theorem neg_add_pos_eq_of_eq_add [s : add_comm_group A] (a b c : A) (H : b = c + a) : -a + b = c :=
  begin apply neg_add_eq_of_eq_add, rewrite add.comm, exact H end

/-theorem neg_add_pos_helper [s : add_comm_group A] (t₁ t₂ e v w₁ w₂ : A) (H₁ : t₁ = -w₁)
        (H₂ : t₂ = w₂) (Hv : w₂ = v) (H : e + w₁ = v) : t₁ + t₂ = e :=
  begin rewrite [H₁, H₂, Hv, -H, add.comm, add_neg_cancel_right] end-/

theorem neg_add_pos_helper1 [s : add_comm_group A] (a b c : A) (H : b + c = a) : -a + b = -c :=
  begin apply neg_add_eq_of_eq_add, apply eq_add_neg_of_add_eq H end

theorem neg_add_pos_helper2 [s : add_comm_group A] (a b c : A) (H : a + c = b) : -a + b = c :=
  begin apply neg_add_eq_of_eq_add, rewrite H end

theorem pos_add_neg_helper [s : add_comm_group A] (a b c : A) (H : b + a = c) : a + b = c :=
  by rewrite [add.comm, H]

theorem sub_eq_add_neg_helper [s : add_comm_group A] (t₁ t₂ e w₁ w₂: A) (H₁ : t₁ = w₁) (H₂ : t₂ = w₂)
        (H : w₁ + -w₂ = e) : t₁ - t₂ = e :=
  by rewrite [sub_eq_add_neg, H₁, H₂, H]

theorem pos_add_pos_helper [s : add_comm_group A] (a b c h₁ h₂ : A) (H₁ : a = h₁) (H₂ : b = h₂)
        (H : h₁ + h₂ = c) : a + b = c :=
  by rewrite [H₁, H₂, H]

theorem subst_into_subtr [s : add_group A] (l r t : A) (prt : l + -r = t) : l - r = t :=
   by rewrite [sub_eq_add_neg, prt]

theorem neg_neg_helper [s : add_group A] (a b : A) (H : a = -b) : -a = b :=
  by rewrite [H, neg_neg]
