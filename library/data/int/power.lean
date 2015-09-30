/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

The power function on the integers.
-/
import data.int.basic data.int.order data.int.div algebra.group_power data.nat.power

namespace int

section migrate_algebra
  open [classes] algebra

  local attribute int.integral_domain [instance]
  local attribute int.linear_ordered_comm_ring [instance]
  local attribute int.decidable_linear_ordered_comm_ring [instance]

  definition pow (a : ℤ) (n : ℕ) : ℤ := algebra.pow a n
  infix [priority int.prio] ^ := pow
  definition nmul (n : ℕ) (a : ℤ) : ℤ := algebra.nmul n a
  infix [priority int.prio] ⬝ := nmul
  definition imul (i : ℤ) (a : ℤ) : ℤ := algebra.imul i a

  migrate from algebra with int
    replacing dvd → dvd, sub → sub, has_le.ge → ge, has_lt.gt → gt, min → min, max → max,
            abs → abs, sign → sign, pow → pow, nmul → nmul, imul → imul
    hiding add_pos_of_pos_of_nonneg,  add_pos_of_nonneg_of_pos,
      add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg, le_add_of_nonneg_of_le,
      le_add_of_le_of_nonneg, lt_add_of_nonneg_of_lt, lt_add_of_lt_of_nonneg,
      lt_of_mul_lt_mul_left, lt_of_mul_lt_mul_right, pos_of_mul_pos_left, pos_of_mul_pos_right
end migrate_algebra

section
  open nat
  theorem of_nat_pow (a n : ℕ) : of_nat (a^n) = (of_nat a)^n :=
  begin
    induction n with n ih,
      apply eq.refl,
    rewrite [pow_succ, nat.pow_succ, of_nat_mul, ih]
  end
end

end int
