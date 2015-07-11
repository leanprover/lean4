/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Binomial coefficients, "n choose k".
-/
import data.nat.div data.nat.fact
open decidable

namespace nat

/- choose -/

definition choose : ℕ → ℕ → ℕ
| 0 0               := 1
| 0 (succ k)        := 0
| (succ n) 0        := 1
| (succ n) (succ k) := choose n (succ k) + choose n k

theorem choose_zero_right (n : ℕ) : choose n 0 = 1 :=
nat.cases_on n rfl (take m, rfl)

theorem choose_zero_succ (k : ℕ) : choose 0 (succ k) = 0 := rfl

theorem choose_succ_succ (n k : ℕ) : choose (succ n) (succ k) = choose n (succ k) + choose n k := rfl

theorem choose_eq_zero_of_lt {n : ℕ} : ∀{k : ℕ}, n < k → choose n k = 0 :=
nat.induction_on n
  (take k, assume H : 0 < k,
    obtain k' (H : k = succ k'), from exists_eq_succ_of_pos H,
    by rewrite H)
  (take n',
    assume IH: ∀ k, n' < k → choose n' k = 0,
    take k,
    assume H : succ n' < k,
    obtain k' (keq : k = succ k'), from exists_eq_succ_of_lt H,
    assert H' : n' < k', by rewrite keq at H; apply lt_of_succ_lt_succ H,
    by rewrite [keq, choose_succ_succ, IH _ H', IH _ (lt.trans H' !lt_succ_self)])

theorem choose_self (n : ℕ) : choose n n = 1 :=
begin
  induction n with [n, ih],
    {apply rfl},
  rewrite [choose_succ_succ, ih, choose_eq_zero_of_lt !lt_succ_self]
end

theorem choose_succ_self (n : ℕ) : choose (succ n) n = succ n :=
begin
  induction n with [n, ih],
    {apply rfl},
  rewrite [choose_succ_succ, ih, choose_self, add.comm]
end

theorem choose_one_right (n : ℕ) : choose n 1 = n :=
begin
  induction n with [n, ih],
    {apply rfl},
  rewrite [choose_succ_succ, ih, choose_zero_right]
end

theorem choose_pos {n : ℕ} : ∀ {k : ℕ}, k ≤ n → choose n k > 0 :=
begin
  induction n with [n, ih],
    {intros [k, H],
      have kz : k = 0, from eq_of_le_of_ge H !zero_le,
      rewrite [kz, choose_zero_right]; apply zero_lt_one},
  intro k,
  cases k with k,
    {intro H, rewrite [choose_zero_right], apply zero_lt_one},
  assume H : succ k ≤ succ n,
  assert H' : k ≤ n, from le_of_succ_le_succ H,
  by rewrite [choose_succ_succ]; apply add_pos_right (ih H')
end

-- A key identity. The proof is subtle.
theorem succ_mul_choose_eq (n : ℕ) : ∀ k, succ n * (choose n k) = choose (succ n) (succ k) * succ k :=
begin
  induction n with [n, ih],
    {intro k,
      cases k with k',
        {rewrite [*choose_self, one_mul, mul_one]},
        {have H : 1 < succ (succ k'), from succ_lt_succ !zero_lt_succ,
          rewrite [one_mul, choose_zero_succ, choose_eq_zero_of_lt H, zero_mul]}},
  intro k,
  cases k with k',
    {rewrite [choose_zero_right, choose_one_right]},
  rewrite [choose_succ_succ (succ n), mul.right_distrib, -ih (succ k')],
  rewrite [choose_succ_succ at {1}, mul.left_distrib, *succ_mul (succ n), mul_succ, -ih k'],
  rewrite [*add.assoc, add.left_comm (choose n _)]
end

theorem choose_mul_fact_mul_fact {n : ℕ} :
  ∀ {k : ℕ}, k ≤ n → choose n k * fact k * fact (n - k) = fact n :=
begin
  induction n using nat.strong_induction_on with [n, ih],
  cases n with n,
    {intro k H, have kz : k = 0, from eq_zero_of_le_zero H, rewrite [kz]},
  intro k,
  intro H,  -- k ≤ n,
  cases k with k,
    {rewrite [choose_zero_right, fact_zero, *one_mul]},
  have kle : k ≤ n, from le_of_succ_le_succ H,
  show choose (succ n) (succ k) * fact (succ k) * fact (succ n - succ k) = fact (succ n), from
  begin
    rewrite [succ_sub_succ, fact_succ, -mul.assoc, -succ_mul_choose_eq],
    rewrite [fact_succ n, -ih n !lt_succ_self kle, *mul.assoc]
  end
end

theorem choose_def_alt {n k : ℕ} (H : k ≤ n) : choose n k = fact n div (fact k * fact (n -k)) :=
eq.symm (div_eq_of_eq_mul_left (mul_pos !fact_pos !fact_pos)
    (by rewrite [-mul.assoc, choose_mul_fact_mul_fact H]))

theorem fact_mul_fact_dvd_fact {n k : ℕ} (H : k ≤ n) : fact k * fact (n - k) ∣ fact n :=
by rewrite [-choose_mul_fact_mul_fact H, mul.assoc]; apply dvd_mul_left

end nat
