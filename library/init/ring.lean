/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
prelude
import init.group

/- Make sure instances defined in this file have lower priority than the ones
   defined for concrete structures -/
set_option default_priority 100

universe variable u

class distrib (α : Type u) extends has_mul α, has_add α :=
(left_distrib : ∀ a b c : α, a * (b + c) = (a * b) + (a * c))
(right_distrib : ∀ a b c : α, (a + b) * c = (a * c) + (b * c))

variable {α : Type u}

lemma left_distrib [distrib α] (a b c : α) : a * (b + c) = a * b + a * c :=
distrib.left_distrib a b c

lemma right_distrib [distrib α] (a b c : α) : (a + b) * c = a * c + b * c :=
distrib.right_distrib a b c

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

structure semiring (α : Type u) extends comm_monoid α renaming
  mul→add mul_assoc→add_assoc one→zero one_mul→zero_add mul_one→add_zero mul_comm→add_comm,
  monoid α, distrib α, mul_zero_class α

attribute [class] semiring

instance add_comm_monoid_of_semiring (α : Type u) [s : semiring α] : add_comm_monoid α :=
@semiring.to_comm_monoid α s

instance monoid_of_semiring (α : Type u) [s : semiring α] : monoid α :=
@semiring.to_monoid α s

instance distrib_of_semiring (α : Type u) [s : semiring α] : distrib α :=
@semiring.to_distrib α s

instance mul_zero_class_of_semiring (α : Type u) [s : semiring α] : mul_zero_class α :=
@semiring.to_mul_zero_class α s

class comm_semiring (α : Type u) extends semiring α, comm_monoid α

/- ring -/

structure ring (α : Type u) extends comm_group α renaming mul→add mul_assoc→add_assoc
  one→zero one_mul→zero_add mul_one→add_zero inv→neg mul_left_inv→add_left_inv mul_comm→add_comm,
  monoid α, distrib α

attribute [class] ring

instance to_add_comm_group_of_ring (α : Type u) [s : ring α] : add_comm_group α :=
@ring.to_comm_group α s

instance monoid_of_ring (α : Type u) [s : ring α] : monoid α :=
@ring.to_monoid α s

instance distrib_of_ring (α : Type u) [s : ring α] : distrib α :=
@ring.to_distrib α s

lemma ring.mul_zero [ring α] (a : α) : a * 0 = 0 :=
have a * 0 + 0 = a * 0 + a * 0, from calc
     a * 0 + 0 = a * (0 + 0)   : by simp
           ... = a * 0 + a * 0 : by rw left_distrib,
show a * 0 = 0, from (add_left_cancel this)^.symm

lemma ring.zero_mul [ring α] (a : α) : 0 * a = 0 :=
have 0 * a + 0 = 0 * a + 0 * a, from calc
  0 * a + 0 = (0 + 0) * a   : by simp
        ... = 0 * a + 0 * a : by rewrite right_distrib,
show 0 * a = 0, from  (add_left_cancel this)^.symm

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

lemma mul_sub_left_distrib [s : ring α] (a b c : α) : a * (b - c) = a * b - a * c :=
calc
   a * (b - c) = a * b + a * -c : left_distrib a b (-c)
           ... = a * b - a * c  : by simp

lemma mul_sub_right_distrib [s : ring α] (a b c : α) : (a - b) * c = a * c - b * c :=
calc
  (a - b) * c = a * c  + -b * c : right_distrib a (-b) c
          ... = a * c - b * c   : by simp
