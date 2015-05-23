/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

The power function on the integers.
-/
import data.int.basic data.int.order data.int.div algebra.group_power

namespace int

section migrate_algebra
  open [classes] algebra

  local attribute int.integral_domain [instance]
  local attribute int.linear_ordered_comm_ring [instance]
  local attribute int.decidable_linear_ordered_comm_ring [instance]

  definition pow (a : ℤ) (n : ℕ) : ℤ := algebra.pow a n
  infix ^ := pow

  migrate from algebra with int
    replacing dvd → dvd, has_le.ge → ge, has_lt.gt → gt, pow → pow
    hiding add_pos_of_pos_of_nonneg,  add_pos_of_nonneg_of_pos,
      add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg, le_add_of_nonneg_of_le,
      le_add_of_le_of_nonneg, lt_add_of_nonneg_of_lt, lt_add_of_lt_of_nonneg,
      lt_of_mul_lt_mul_left, lt_of_mul_lt_mul_right, pos_of_mul_pos_left, pos_of_mul_pos_right
end migrate_algebra

end int
