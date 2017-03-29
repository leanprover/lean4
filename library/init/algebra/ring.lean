/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
prelude
import init.algebra.group

/- Make sure instances defined in this file have lower priority than the ones
   defined for concrete structures -/
set_option default_priority 100

universe u

class distrib (α : Type u) extends has_mul α, has_add α :=
(left_distrib : ∀ a b c : α, a * (b + c) = (a * b) + (a * c))
(right_distrib : ∀ a b c : α, (a + b) * c = (a * c) + (b * c))

variable {α : Type u}

lemma left_distrib [distrib α] (a b c : α) : a * (b + c) = a * b + a * c :=
distrib.left_distrib a b c

def mul_add := @left_distrib

lemma right_distrib [distrib α] (a b c : α) : (a + b) * c = a * c + b * c :=
distrib.right_distrib a b c

def add_mul := @right_distrib

class mul_zero_class (α : Type u) extends has_mul α, has_zero α :=
(zero_mul : ∀ a : α, 0 * a = 0)
(mul_zero : ∀ a : α, a * 0 = 0)

@[simp] lemma zero_mul [mul_zero_class α] (a : α) : 0 * a = 0 :=
mul_zero_class.zero_mul a

@[simp] lemma mul_zero [mul_zero_class α] (a : α) : a * 0 = 0 :=
mul_zero_class.mul_zero a

class zero_ne_one_class (α : Type u) extends has_zero α, has_one α :=
(zero_ne_one : 0 ≠ (1:α))

lemma zero_ne_one [s: zero_ne_one_class α] : 0 ≠ (1:α) :=
@zero_ne_one_class.zero_ne_one α s

/- semiring -/

class semiring (α : Type u) extends add_comm_monoid α, monoid α, distrib α, mul_zero_class α

section semiring
  variables [semiring α]

  lemma one_add_one_eq_two : 1 + 1 = (2 : α) :=
  begin unfold bit0, reflexivity end

  lemma ne_zero_of_mul_ne_zero_right {a b : α} (h : a * b ≠ 0) : a ≠ 0 :=
  suppose a = 0,
  have a * b = 0, by rw [this, zero_mul],
  h this

  lemma ne_zero_of_mul_ne_zero_left {a b : α} (h : a * b ≠ 0) : b ≠ 0 :=
  suppose b = 0,
  have a * b = 0, by rw [this, mul_zero],
  h this

  lemma distrib_three_right (a b c d : α) : (a + b + c) * d = a * d + b * d + c * d :=
  by simp [right_distrib]
end semiring

class comm_semiring (α : Type u) extends semiring α, comm_monoid α

/- ring -/

class ring (α : Type u) extends add_comm_group α, monoid α, distrib α

lemma ring.mul_zero [ring α] (a : α) : a * 0 = 0 :=
have a * 0 + 0 = a * 0 + a * 0, from calc
     a * 0 + 0 = a * (0 + 0)   : by simp
           ... = a * 0 + a * 0 : by rw left_distrib,
show a * 0 = 0, from (add_left_cancel this).symm

lemma ring.zero_mul [ring α] (a : α) : 0 * a = 0 :=
have 0 * a + 0 = 0 * a + 0 * a, from calc
  0 * a + 0 = (0 + 0) * a   : by simp
        ... = 0 * a + 0 * a : by rewrite right_distrib,
show 0 * a = 0, from  (add_left_cancel this).symm

instance ring.to_semiring [s : ring α] : semiring α :=
{ s with
  mul_zero := ring.mul_zero,
  zero_mul := ring.zero_mul }

lemma neg_mul_eq_neg_mul [s : ring α] (a b : α) : -(a * b) = -a * b :=
neg_eq_of_add_eq_zero
  begin rw [-right_distrib, add_right_neg, zero_mul] end

lemma neg_mul_eq_mul_neg [s : ring α] (a b : α) : -(a * b) = a * -b :=
neg_eq_of_add_eq_zero
  begin rw [-left_distrib, add_right_neg, mul_zero] end

@[simp] lemma neg_mul_eq_neg_mul_symm [s : ring α] (a b : α) : - a * b = - (a * b) :=
eq.symm (neg_mul_eq_neg_mul a b)

@[simp] lemma mul_neg_eq_neg_mul_symm [s : ring α] (a b : α) : a * - b = - (a * b) :=
eq.symm (neg_mul_eq_mul_neg a b)

lemma neg_mul_neg [s : ring α] (a b : α) : -a * -b = a * b :=
by simp

lemma neg_mul_comm [s : ring α] (a b : α) : -a * b = a * -b :=
by simp

theorem neg_eq_neg_one_mul [s : ring α] (a : α) : -a = -1 * a :=
by simp

lemma mul_sub_left_distrib [s : ring α] (a b c : α) : a * (b - c) = a * b - a * c :=
calc
   a * (b - c) = a * b + a * -c : left_distrib a b (-c)
           ... = a * b - a * c  : by simp

def mul_sub := @mul_sub_left_distrib

lemma mul_sub_right_distrib [s : ring α] (a b c : α) : (a - b) * c = a * c - b * c :=
calc
  (a - b) * c = a * c  + -b * c : right_distrib a (-b) c
          ... = a * c - b * c   : by simp

def sub_mul := @mul_sub_right_distrib

class comm_ring (α : Type u) extends ring α, comm_semigroup α

instance comm_ring.to_comm_semiring [s : comm_ring α] : comm_semiring α :=
{ s with
  mul_zero := mul_zero,
  zero_mul := zero_mul }

section comm_ring
  variable [comm_ring α]

  lemma mul_self_sub_mul_self_eq (a b : α) : a * a - b * b = (a + b) * (a - b) :=
  by simp [right_distrib, left_distrib]

  lemma mul_self_sub_one_eq (a : α) : a * a - 1 = (a + 1) * (a - 1) :=
  by simp [right_distrib, left_distrib]

  lemma add_mul_self_eq (a b : α) : (a + b) * (a + b) = a*a + 2*a*b + b*b :=
  calc (a + b)*(a + b) = a*a + (1+1)*a*b + b*b : by simp [right_distrib, left_distrib]
               ...     = a*a + 2*a*b + b*b     : by rw one_add_one_eq_two
end comm_ring

class no_zero_divisors (α : Type u) extends has_mul α, has_zero α :=
(eq_zero_or_eq_zero_of_mul_eq_zero : ∀ a b : α, a * b = 0 → a = 0 ∨ b = 0)

lemma eq_zero_or_eq_zero_of_mul_eq_zero [no_zero_divisors α] {a b : α} (h : a * b = 0) : a = 0 ∨ b = 0 :=
no_zero_divisors.eq_zero_or_eq_zero_of_mul_eq_zero a b h

lemma eq_zero_of_mul_self_eq_zero [no_zero_divisors α] {a : α} (h : a * a = 0) : a = 0 :=
or.elim (eq_zero_or_eq_zero_of_mul_eq_zero h) (assume h', h') (assume h', h')

class integral_domain (α : Type u) extends comm_ring α, no_zero_divisors α, zero_ne_one_class α

section integral_domain
  variable [integral_domain α]

  lemma mul_ne_zero {a b : α} (h₁ : a ≠ 0) (h₂ : b ≠ 0) : a * b ≠ 0 :=
  λ h, or.elim (eq_zero_or_eq_zero_of_mul_eq_zero h) (assume h₃, h₁ h₃) (assume h₄, h₂ h₄)

  lemma eq_of_mul_eq_mul_right {a b c : α} (ha : a ≠ 0) (h : b * a = c * a) : b = c :=
  have b * a - c * a = 0, from sub_eq_zero_of_eq h,
  have (b - c) * a = 0,   by rw [mul_sub_right_distrib, this],
  have b - c = 0,         from (eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_right ha,
  eq_of_sub_eq_zero this

  lemma eq_of_mul_eq_mul_left {a b c : α} (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
  have a * b - a * c = 0, from sub_eq_zero_of_eq h,
  have a * (b - c) = 0,   by rw [mul_sub_left_distrib, this],
  have b - c = 0,         from (eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_left ha,
  eq_of_sub_eq_zero this

  lemma eq_zero_of_mul_eq_self_right {a b : α} (h₁ : b ≠ 1) (h₂ : a * b = a) : a = 0 :=
  have hb : b - 1 ≠ 0, from
    suppose b - 1 = 0,
    have b = 0 + 1, from eq_add_of_sub_eq this,
    have b = 1,     by rwa zero_add at this,
    h₁ this,
  have a * b - a = 0,   by simp [h₂],
  have a * (b - 1) = 0, by rwa [mul_sub_left_distrib, mul_one],
    show a = 0, from (eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_right hb

  lemma eq_zero_of_mul_eq_self_left {a b : α} (h₁ : b ≠ 1) (h₂ : b * a = a) : a = 0 :=
  eq_zero_of_mul_eq_self_right h₁ (by rwa mul_comm at h₂)

  lemma mul_self_eq_mul_self_iff (a b : α) : a * a = b * b ↔ a = b ∨ a = -b :=
  iff.intro
    (suppose a * a = b * b,
      have (a - b) * (a + b) = 0,
        by rewrite [mul_comm, -mul_self_sub_mul_self_eq, this, sub_self],
      have a - b = 0 ∨ a + b = 0, from eq_zero_or_eq_zero_of_mul_eq_zero this,
      or.elim this
        (suppose a - b = 0, or.inl (eq_of_sub_eq_zero this))
        (suppose a + b = 0, or.inr (eq_neg_of_add_eq_zero this)))
    (suppose a = b ∨ a = -b, or.elim this
      (suppose a = b,  by rewrite this)
      (suppose a = -b, by rewrite [this, neg_mul_neg]))

  lemma mul_self_eq_one_iff (a : α) : a * a = 1 ↔ a = 1 ∨ a = -1 :=
  have a * a = 1 * 1 ↔ a = 1 ∨ a = -1, from mul_self_eq_mul_self_iff a 1,
  by rwa mul_one at this

end integral_domain

/- TODO(Leo): remove the following annotations as soon as we have support for arithmetic
   in the SMT tactic framework -/
attribute [ematch] add_zero zero_add mul_one one_mul mul_zero zero_mul
