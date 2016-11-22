/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.group

universe variable u
variable α : Type u

class distrib (α : Type u) extends has_mul α, has_add α :=
(left_distrib : ∀ a b c : α, a * (b + c) = (a * b) + (a * c))
(right_distrib : ∀ a b c : α, (a + b) * c = (a * c) + (b * c))

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

instance monoid_of_ring (α : Type u) [s : ring α] : monoid α := @ring.to_monoid α s

instance distrib_of_ring (α : Type u) [s : ring α] : distrib α :=
@ring.to_distrib α s
