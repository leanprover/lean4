/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad

The power function on the natural numbers.
-/
import data.nat.basic data.nat.order data.nat.div algebra.group_power

namespace nat

section migrate_algebra
  open [classes] algebra
  local attribute nat.comm_semiring [instance]
  local attribute nat.linear_ordered_semiring [instance]

  definition pow (a : ℕ) (n : ℕ) : ℕ := algebra.pow a n
  migrate from algebra with nat
    replacing dvd → dvd, has_le.ge → ge, has_lt.gt → gt, pow → pow
    hiding add_pos_of_pos_of_nonneg,  add_pos_of_nonneg_of_pos,
      add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg, le_add_of_nonneg_of_le,
      le_add_of_le_of_nonneg, lt_add_of_nonneg_of_lt, lt_add_of_lt_of_nonneg,
      lt_of_mul_lt_mul_left, lt_of_mul_lt_mul_right, pos_of_mul_pos_left, pos_of_mul_pos_right
end migrate_algebra

-- TODO: eventually this will be subsumed under the algebraic theorems

theorem mul_self_eq_pow_2 (a : nat) : a * a = pow a 2 :=
show a * a = pow a (succ (succ zero)), from
by rewrite [*pow_succ, *pow_zero, one_mul]

theorem pow_cancel_left : ∀ {a b c : nat}, a > 1 → pow a b = pow a c → b = c
| a 0        0        h₁ h₂ := rfl
| a (succ b) 0        h₁ h₂ :=
  assert aeq1 : a = 1, by rewrite [pow_succ' at h₂, pow_zero at h₂]; exact (eq_one_of_mul_eq_one_right h₂),
  assert h₁   : 1 < 1, by rewrite [aeq1 at h₁]; exact h₁,
  absurd h₁ !lt.irrefl
| a 0        (succ c) h₁ h₂ :=
  assert aeq1 : a = 1, by rewrite [pow_succ' at h₂, pow_zero at h₂]; exact (eq_one_of_mul_eq_one_right (eq.symm h₂)),
  assert h₁   : 1 < 1, by rewrite [aeq1 at h₁]; exact h₁,
  absurd h₁ !lt.irrefl
| a (succ b) (succ c) h₁ h₂ :=
  assert ane0 : a ≠ 0, from assume aeq0, by rewrite [aeq0 at h₁]; exact (absurd h₁ dec_trivial),
  assert beqc : pow a b = pow a c, by rewrite [*pow_succ' at h₂]; exact (mul_cancel_left_of_ne_zero ane0 h₂),
  by rewrite [pow_cancel_left h₁ beqc]

theorem pow_div_cancel : ∀ {a b : nat}, a ≠ 0 → pow a (succ b) div a = pow a b
| a 0        h := by rewrite [pow_succ', pow_zero, mul_one, div_self (pos_of_ne_zero h)]
| a (succ b) h := by rewrite [pow_succ', mul_div_cancel_left _ (pos_of_ne_zero h)]
end nat
