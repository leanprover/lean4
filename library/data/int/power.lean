/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

The power function on the integers.
-/
import data.int.basic data.int.order data.int.div algebra.group_power data.nat.power

namespace int
open - [notations] algebra

definition int_has_pow_nat : has_pow_nat int :=
has_pow_nat.mk pow_nat

/-
  definition nmul (n : ℕ) (a : ℤ) : ℤ := algebra.nmul n a
  infix [priority int.prio] ⬝ := nmul
  definition imul (i : ℤ) (a : ℤ) : ℤ := algebra.imul i a
-/

open nat
theorem of_nat_pow (a n : ℕ) : of_nat (a^n) = (of_nat a)^n :=
begin
  induction n with n ih,
    apply eq.refl,
  rewrite [pow_succ, pow_succ, of_nat_mul, ih]
end

end int
