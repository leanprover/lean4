/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Factorial
-/
import data.nat.div

namespace nat
definition fact : nat → nat
| 0        := 1
| (succ n) := (succ n) * fact n

lemma fact_zero : fact 0 = 1 :=
rfl

lemma fact_one : fact 1 = 1 :=
rfl

lemma fact_succ (n) : fact (succ n) = succ n * fact n :=
rfl

lemma fact_ne_zero : ∀ n, fact n ≠ 0
| 0        := by contradiction
| (succ n) :=
  begin
    intro h,
    rewrite [fact_succ at h],
    cases (eq_zero_or_eq_zero_of_mul_eq_zero h) with h₁ h₂,
      contradiction,
      exact fact_ne_zero n h₂
  end

lemma fact_gt_0 (n) : fact n > 0 :=
pos_of_ne_zero (fact_ne_zero n)

lemma dvd_fact : ∀ {m n}, m > 0 → m ≤ n → m ∣ fact n
| m 0        h₁ h₂ := absurd h₁ (not_lt_of_ge h₂)
| m (succ n) h₁ h₂ :=
  begin
    rewrite fact_succ,
    cases (eq_or_lt_of_le h₂) with he hl,
      {subst m, apply dvd_mul_right},
      {have aux : m ∣ fact n, from dvd_fact h₁ (le_of_lt_succ hl),
       apply dvd_mul_of_dvd_right aux}
  end

lemma fact_le {m n} : m ≤ n → fact m ≤ fact n :=
begin
  induction n with n ih,
   {intro h,
    have meq0 : m = 0, from eq_zero_of_le_zero h,
    subst m},
   {intro m_le_succ_n,
    cases (eq_or_lt_of_le m_le_succ_n) with h₁ h₂,
      {subst m},
      {transitivity (fact n),
        exact ih (le_of_lt_succ h₂),
        rewrite [fact_succ, -one_mul at {1}],
        exact mul_le_mul (succ_le_succ (zero_le n)) !le.refl}}
end
end nat
