/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Parity
-/
import data.nat.div logic.identities

namespace nat
open decidable

definition even (n : nat) := n mod 2 = 0

definition decidable_even [instance] : ∀ n, decidable (even n) :=
take n, !nat.has_decidable_eq

definition odd (n : nat) := ¬even n

definition decidable_odd [instance] : ∀ n, decidable (odd n) :=
take n, decidable_not

lemma even_of_dvd {n} : 2 ∣ n → even n :=
mod_eq_zero_of_dvd

lemma dvd_of_even {n} : even n → 2 ∣ n :=
dvd_of_mod_eq_zero

lemma not_odd_zero : ¬ odd 0 :=
dec_trivial

lemma even_zero : even 0 :=
dec_trivial

lemma odd_one : odd 1 :=
dec_trivial

lemma not_even_one : ¬ even 1 :=
dec_trivial

lemma odd_eq_not_even (n : nat) : odd n = ¬ even n :=
rfl

lemma odd_iff_not_even (n : nat) : odd n ↔ ¬ even n :=
!iff.refl

lemma odd_of_not_even {n} : ¬ even n → odd n :=
suppose ¬ even n,
iff.mpr !odd_iff_not_even this

lemma even_of_not_odd {n} : ¬ odd n → even n :=
suppose ¬ odd n,
not_not_elim (iff.mp (not_iff_not_of_iff !odd_iff_not_even) this)

lemma not_odd_of_even {n} : even n → ¬ odd n :=
suppose even n,
iff.mpr (not_iff_not_of_iff !odd_iff_not_even) (not_not_intro this)

lemma not_even_of_odd {n} : odd n → ¬ even n :=
suppose odd n,
iff.mp !odd_iff_not_even this

lemma odd_succ_of_even {n} : even n → odd (succ n) :=
suppose even n,
by_contradiction (suppose ¬ odd (succ n),
  assert 0 = 1, from calc
    0  = (n+1) mod 2 : even_of_not_odd this
   ... = 1 mod 2     : add_mod_eq_add_mod_right 1 `even n`,
  by contradiction)

lemma eq_1_of_ne_0_lt_2 : ∀ {n : nat}, n ≠ 0 → n < 2 → n = 1
| 0     h₁ h₂ := absurd rfl h₁
| 1     h₁ h₂ := rfl
| (n+2) h₁ h₂ := absurd (lt_of_succ_lt_succ (lt_of_succ_lt_succ h₂)) !not_lt_zero

lemma mod_eq_of_odd {n} : odd n → n mod 2 = 1 :=
suppose odd n,
  have ¬ n mod 2 = 0, from this,
  have n mod 2 < 2,   from mod_lt n dec_trivial,
  eq_1_of_ne_0_lt_2 `¬ n mod 2 = 0` `n mod 2 < 2`

lemma odd_of_mod_eq {n} : n mod 2 = 1 → odd n :=
suppose n mod 2 = 1,
by_contradiction (suppose ¬ odd n,
  assert n mod 2 = 0, from even_of_not_odd this,
  by rewrite this at *; contradiction)

lemma even_succ_of_odd {n} : odd n → even (succ n) :=
suppose odd n,
  assert n mod 2 = 1 mod 2,     from mod_eq_of_odd this,
  assert (n+1) mod 2 = 2 mod 2, from add_mod_eq_add_mod_right 1 this,
  by rewrite mod_self at this; exact this

lemma odd_succ_succ_of_odd {n} : odd n → odd (succ (succ n)) :=
suppose odd n,
odd_succ_of_even (even_succ_of_odd this)

lemma even_succ_succ_of_even {n} : even n → even (succ (succ n)) :=
suppose even n,
even_succ_of_odd (odd_succ_of_even this)

lemma even_of_odd_succ {n} : odd (succ n) → even n :=
suppose odd (succ n),
by_contradiction (suppose ¬ even n,
  have odd n,         from odd_of_not_even this,
  have even (succ n), from even_succ_of_odd this,
  absurd this (not_even_of_odd `odd (succ n)`))

lemma odd_of_even_succ {n} : even (succ n) → odd n :=
suppose even (succ n),
by_contradiction (suppose ¬ odd n,
  have even n,       from even_of_not_odd this,
  have odd (succ n), from odd_succ_of_even this,
  absurd `even (succ n)` (not_even_of_odd this))

lemma even_of_even_succ_succ {n} : even (succ (succ n)) → even n :=
suppose even (n+2),
even_of_odd_succ (odd_of_even_succ this)

lemma odd_of_odd_succ_succ {n} : odd (succ (succ n)) → odd n :=
suppose odd (n+2),
odd_of_even_succ (even_of_odd_succ this)

lemma dvd_of_odd {n} : odd n → 2 ∣ n+1 :=
suppose odd n,
dvd_of_even (even_succ_of_odd this)

lemma odd_of_dvd {n} : 2 ∣ n+1 → odd n :=
suppose 2 ∣ n+1,
odd_of_even_succ (even_of_dvd this)

lemma even_two_mul : ∀ n, even (2 * n) :=
take n, even_of_dvd (dvd_mul_right 2 n)

lemma odd_two_mul_plus_one : ∀ n, odd (2 * n + 1) :=
take n, odd_succ_of_even (even_two_mul n)

lemma not_even_two_mul_plus_one : ∀ n, ¬ even (2 * n + 1) :=
take n, not_even_of_odd (odd_two_mul_plus_one n)

lemma not_odd_two_mul : ∀ n, ¬ odd (2 * n) :=
take n, not_odd_of_even (even_two_mul n)

lemma even_pred_of_odd : ∀ {n}, odd n → even (pred n)
| 0     h := absurd h not_odd_zero
| (n+1) h := even_of_odd_succ h

lemma even_or_odd : ∀ n, even n ∨ odd n :=
λ n, by_cases
  (λ h : even n,   or.inl h)
  (λ h : ¬ even n, or.inr (odd_of_not_even h))

lemma exists_of_even {n} : even n → ∃ k, n = 2*k :=
λ h, exists_eq_mul_right_of_dvd (dvd_of_even h)

lemma exists_of_odd : ∀ {n}, odd n → ∃ k, n = 2*k + 1
| 0 h     := absurd h not_odd_zero
| (n+1) h :=
  obtain k (hk : n = 2*k), from exists_of_even (even_of_odd_succ h),
  exists.intro k (by subst n)

lemma even_of_exists {n} : (∃ k, n = 2 * k) → even n :=
suppose ∃ k, n = 2 * k,
obtain k (hk : n = 2 * k), from this,
have 2 ∣ n, by subst n; apply dvd_mul_right,
even_of_dvd this

lemma odd_of_exists {n} : (∃ k, n = 2 * k + 1) → odd n :=
assume h, by_contradiction (λ hn,
  have even n, from even_of_not_odd hn,
  have ∃ k, n = 2 * k, from exists_of_even this,
  obtain k₁ (hk₁ : n = 2 * k₁ + 1), from h,
  obtain k₂ (hk₂ : n = 2 * k₂), from this,
  assert (2 * k₁ + 1) mod 2 = (2 * k₂) mod 2, by rewrite [-hk₁, -hk₂],
  begin
    rewrite [mul_mod_right at this, add.comm at this, add_mul_mod_self_left at this],
    contradiction
  end)

lemma even_add_of_even_of_even {n m} : even n → even m → even (n+m) :=
suppose even n, suppose even m,
obtain k₁ (hk₁ : n = 2 * k₁), from exists_of_even `even n`,
obtain k₂ (hk₂ : m = 2 * k₂), from exists_of_even `even m`,
even_of_exists (exists.intro (k₁+k₂) (by rewrite [hk₁, hk₂, mul.left_distrib]))

lemma even_add_of_odd_of_odd {n m} : odd n → odd m → even (n+m) :=
suppose odd n, suppose odd m,
assert even (succ n + succ m),    from even_add_of_even_of_even (even_succ_of_odd `odd n`) (even_succ_of_odd `odd m`),
have   even(succ (succ (n + m))), by rewrite [add_succ at this, succ_add at this]; exact this,
even_of_even_succ_succ this

lemma odd_add_of_even_of_odd {n m} : even n → odd m → odd (n+m) :=
suppose even n, suppose odd m,
assert even (n + succ m), from even_add_of_even_of_even `even n` (even_succ_of_odd `odd m`),
odd_of_even_succ this

lemma odd_add_of_odd_of_even {n m} : odd n → even m → odd (n+m) :=
suppose odd n, suppose even m,
assert odd (m+n), from odd_add_of_even_of_odd `even m` `odd n`,
by rewrite add.comm at this; exact this

lemma even_mul_of_even_left {n} (m) : even n → even (n*m) :=
suppose even n,
obtain k (hk : n = 2*k), from exists_of_even this,
even_of_exists (exists.intro (k*m) (by rewrite [hk, mul.assoc]))

lemma even_mul_of_even_right {n} (m) : even n → even (m*n) :=
suppose even n,
assert even (n*m), from even_mul_of_even_left _ this,
by rewrite mul.comm at this; exact this

lemma odd_mul_of_odd_of_odd {n m} : odd n → odd m → odd (n*m) :=
suppose odd n, suppose odd m,
assert even (n * succ m), from even_mul_of_even_right _ (even_succ_of_odd `odd m`),
assert even (n * m + n),  by rewrite mul_succ at this; exact this,
by_contradiction (suppose ¬ odd (n*m),
  assert even (n*m), from even_of_not_odd this,
  absurd `even (n * m + n)` (not_even_of_odd (odd_add_of_even_of_odd this `odd n`)))

end nat
