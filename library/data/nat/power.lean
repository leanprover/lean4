/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad

The power function on the natural numbers.
-/
import data.nat.basic data.nat.order data.nat.div data.nat.gcd algebra.ring_power

namespace nat

section migrate_algebra
  open [classes] algebra
  local attribute nat.comm_semiring [instance]
  local attribute nat.linear_ordered_semiring [instance]

  definition pow (a : ℕ) (n : ℕ) : ℕ := algebra.pow a n
  infix ^ := pow

  theorem pow_le_pow_of_le {x y : ℕ} (i : ℕ) (H : x ≤ y) : x^i ≤ y^i :=
  algebra.pow_le_pow_of_le i !zero_le H

  migrate from algebra with nat
    replacing dvd → dvd, has_le.ge → ge, has_lt.gt → gt, pow → pow
    hiding add_pos_of_pos_of_nonneg,  add_pos_of_nonneg_of_pos,
      add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg, le_add_of_nonneg_of_le,
      le_add_of_le_of_nonneg, lt_add_of_nonneg_of_lt, lt_add_of_lt_of_nonneg,
      lt_of_mul_lt_mul_left, lt_of_mul_lt_mul_right, pos_of_mul_pos_left, pos_of_mul_pos_right,
      pow_nonneg_of_nonneg
end migrate_algebra

-- generalize to semirings?
theorem le_pow_self {x : ℕ} (H : x > 1) : ∀ i, i ≤ x^i
| 0        := !zero_le
| (succ j) := have x > 0, from lt.trans zero_lt_one H,
              have x^j ≥ 1, from succ_le_of_lt (pow_pos_of_pos _ this),
              have x ≥ 2, from succ_le_of_lt H,
              calc
                succ j = j + 1         : rfl
                   ... ≤ x^j + 1       : add_le_add_right (le_pow_self j)
                   ... ≤ x^j + x^j     : add_le_add_left `x^j ≥ 1`
                   ... = x^j * (1 + 1) : by rewrite [mul.left_distrib, *mul_one]
                   ... = x^j * 2       : rfl
                   ... ≤ x^j * x       : mul_le_mul_left _ `x ≥ 2`
                   ... = x^(succ j)    : rfl

-- TODO: eventually this will be subsumed under the algebraic theorems

theorem mul_self_eq_pow_2 (a : nat) : a * a = pow a 2 :=
show a * a = pow a (succ (succ zero)), from
by rewrite [*pow_succ, *pow_zero, one_mul]

theorem pow_cancel_left : ∀ {a b c : nat}, a > 1 → pow a b = pow a c → b = c
| a 0        0        h₁ h₂ := rfl
| a (succ b) 0        h₁ h₂ :=
  assert a = 1, by rewrite [pow_succ' at h₂, pow_zero at h₂]; exact (eq_one_of_mul_eq_one_right h₂),
  assert 1 < 1, by rewrite [this at h₁]; exact h₁,
  absurd `1 < 1` !lt.irrefl
| a 0        (succ c) h₁ h₂ :=
  assert a = 1, by rewrite [pow_succ' at h₂, pow_zero at h₂]; exact (eq_one_of_mul_eq_one_right (eq.symm h₂)),
  assert 1 < 1, by rewrite [this at h₁]; exact h₁,
  absurd `1 < 1` !lt.irrefl
| a (succ b) (succ c) h₁ h₂ :=
  assert a ≠ 0, from assume aeq0, by rewrite [aeq0 at h₁]; exact (absurd h₁ dec_trivial),
  assert pow a b = pow a c, by rewrite [*pow_succ' at h₂]; exact (eq_of_mul_eq_mul_left (pos_of_ne_zero this) h₂),
  by rewrite [pow_cancel_left h₁ this]

theorem pow_div_cancel : ∀ {a b : nat}, a ≠ 0 → pow a (succ b) div a = pow a b
| a 0        h := by rewrite [pow_succ', pow_zero, mul_one, div_self (pos_of_ne_zero h)]
| a (succ b) h := by rewrite [pow_succ', mul_div_cancel_left _ (pos_of_ne_zero h)]

lemma dvd_pow : ∀ (i : nat) {n : nat}, n > 0 → i ∣ i^n
| i 0        h := absurd h !lt.irrefl
| i (succ n) h := by rewrite [pow_succ]; apply dvd_mul_left

lemma dvd_pow_of_dvd_of_pos : ∀ {i j n : nat}, i ∣ j → n > 0 → i ∣ j^n
| i j 0        h₁ h₂ := absurd h₂ !lt.irrefl
| i j (succ n) h₁ h₂ := by rewrite [pow_succ]; apply dvd_mul_of_dvd_right h₁

lemma pow_mod_eq_zero (i : nat) {n : nat} (h : n > 0) : (i^n) mod i = 0 :=
iff.mp !dvd_iff_mod_eq_zero (dvd_pow i h)

lemma pow_dvd_of_pow_succ_dvd {p i n : nat} : p^(succ i) ∣ n → p^i ∣ n :=
suppose p^(succ i) ∣ n,
assert p^i ∣ p^(succ i), from by rewrite [pow_succ]; apply dvd_of_eq_mul; apply rfl,
dvd.trans `p^i ∣ p^(succ i)` `p^(succ i) ∣ n`

lemma dvd_of_pow_succ_dvd_mul_pow {p i n : nat} (Ppos : p > 0) :
  p^(succ i) ∣ (n * p^i) → p ∣ n :=
by rewrite [pow_succ']; apply dvd_of_mul_dvd_mul_right; apply pow_pos_of_pos _ Ppos

lemma coprime_pow_right {a b} : ∀ n, coprime b a → coprime b (a^n)
| 0        h := !comprime_one_right
| (succ n) h :=
  begin
    rewrite [pow_succ],
    apply coprime_mul_right,
      exact coprime_pow_right n h,
      exact h
  end

lemma coprime_pow_left {a b} : ∀ n, coprime b a → coprime (b^n) a :=
take n, suppose coprime b a,
coprime_swap (coprime_pow_right n (coprime_swap this))

end nat
