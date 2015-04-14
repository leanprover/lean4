/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.nat.power
Authors: Leonardo de Moura

Power
-/
import data.nat.basic data.nat.div

namespace nat

definition pow : nat → nat → nat
| a  0        := 1
| a  (succ b) := a * pow a b

theorem pow_zero (a : nat) : pow a 0 = 1 :=
rfl

theorem pow_succ (a b : nat) : pow a (succ b) = a * pow a b :=
rfl

theorem one_pow : ∀ (a : nat), pow 1 a = 1
| 0        := rfl
| (succ a) := by rewrite [pow_succ, one_pow]

theorem pow_one : ∀ {a : nat}, a ≠ 0 → pow a 1 = a
| 0        h := absurd rfl h
| (succ a) h := by rewrite [pow_succ, pow_zero, mul_one]

theorem zero_pow : ∀ {a : nat}, a ≠ 0 → pow 0 a = 0
| 0        h := absurd rfl h
| (succ a) h := by rewrite [pow_succ, zero_mul]

theorem pow_add : ∀ (a b c : nat), pow a (b + c) = pow a b * pow a c
| a b 0        := by rewrite [add_zero, pow_zero, mul_one]
| a b (succ c) := by rewrite [add_succ, *pow_succ, pow_add a b c, mul.left_comm]

theorem mul_self_eq_pow_2 (a : nat) : a * a = pow a 2 :=
show a * a = pow a (succ (succ zero)), from
by rewrite [*pow_succ, *pow_zero, mul_one]

theorem pow_cancel_left : ∀ {a b c : nat}, a > 1 → pow a b = pow a c → b = c
| a 0        0        h₁ h₂ := rfl
| a (succ b) 0        h₁ h₂ :=
  assert aeq1 : a = 1, by rewrite [pow_succ at h₂, pow_zero at h₂]; exact (eq_one_of_mul_eq_one_right h₂),
  assert h₁   : 1 < 1, by rewrite [aeq1 at h₁]; exact h₁,
  absurd h₁ !lt.irrefl
| a 0        (succ c) h₁ h₂ :=
  assert aeq1 : a = 1, by rewrite [pow_succ at h₂, pow_zero at h₂]; exact (eq_one_of_mul_eq_one_right (eq.symm h₂)),
  assert h₁   : 1 < 1, by rewrite [aeq1 at h₁]; exact h₁,
  absurd h₁ !lt.irrefl
| a (succ b) (succ c) h₁ h₂ :=
  assert ane0 : a ≠ 0, from assume aeq0, by rewrite [aeq0 at h₁]; exact (absurd h₁ dec_trivial),
  assert beqc : pow a b = pow a c, by rewrite [*pow_succ at h₂]; exact (mul_cancel_left_of_ne_zero ane0 h₂),
  by rewrite [pow_cancel_left h₁ beqc]

theorem pow_div_cancel : ∀ {a b : nat}, a ≠ 0 → pow a (succ b) div a = pow a b
| a 0        h := by rewrite [pow_succ, pow_zero, mul_one, div_self (pos_of_ne_zero h)]
| a (succ b) h := by rewrite [pow_succ, mul_div_cancel_left _ (pos_of_ne_zero h)]
end nat
