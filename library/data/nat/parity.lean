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
λ n, !nat.has_decidable_eq

definition odd (n : nat) := ¬even n

definition decidable_odd [instance] : ∀ n, decidable (odd n) :=
λ n, decidable_not

lemma not_odd_zero : ¬ odd 0 :=
dec_trivial

lemma even_zero : even 0 :=
dec_trivial

lemma odd_one : odd 1 :=
dec_trivial

lemma not_even_one : ¬ even 1 :=
dec_trivial

lemma odd_eq_not_even : ∀ n, odd n = ¬ even n :=
λ n, rfl

lemma odd_iff_not_even : ∀ n, odd n ↔ ¬ even n :=
λ n, !iff.refl

lemma odd_of_not_even : ∀ {n}, ¬ even n → odd n :=
λ n h, iff.mp' !odd_iff_not_even h

lemma even_of_not_odd : ∀ {n}, ¬ odd n → even n :=
λ n h, not_not_elim (iff.mp (not_iff_not_of_iff !odd_iff_not_even) h)

lemma not_odd_of_even : ∀ {n}, even n → ¬ odd n :=
λ n h, iff.mp' (not_iff_not_of_iff !odd_iff_not_even) (not_not_intro h)

lemma not_even_of_odd : ∀ {n}, odd n → ¬ even n :=
λ n h, iff.mp !odd_iff_not_even h

lemma odd_succ_of_even : ∀ {n}, even n → odd (succ n) :=
begin
  intro n, esimp [even, odd], intro h, rewrite [-add_one],
  have h₁ : n mod 2 = 0 mod 2, from h,
  have h₂ : (n+1) mod 2 = 1,   from add_mod_eq_add_mod_right 1 h₁,
  rewrite h₂, contradiction
end

lemma even_succ_of_odd : ∀ {n}, odd n → even (succ n) :=
begin
  intro n, esimp [even, odd], intro h, rewrite [-add_one],
  have h₁ : n mod 2 < 2, from mod_lt n dec_trivial,
  have h₂ : n mod 2 = 1, begin
    revert h h₁, generalize (n mod 2), intro x, cases x, {intro h', exact absurd rfl h'}, cases a,
      {intros, reflexivity},
      {intro h hl, exact absurd (lt_of_succ_lt_succ (lt_of_succ_lt_succ hl)) !not_lt_zero}
  end,
  have h₃ : n mod 2 = 1 mod 2, from h₂,
  have h₄ : (n+1) mod 2 = 0, from add_mod_eq_add_mod_right 1 h₃,
  rewrite h₄
end

lemma odd_succ_succ_of_odd : ∀ {n}, odd n → odd (succ (succ n)) :=
λ n h, odd_succ_of_even (even_succ_of_odd h)

lemma even_succ_succ_of_even : ∀ {n}, even n → even (succ (succ n)) :=
λ n h, even_succ_of_odd (odd_succ_of_even h)

lemma even_of_odd_succ : ∀ {n}, odd (succ n) → even n :=
λ n h, by_contradiction (λ he,
  have h₁ : odd n, from odd_of_not_even he,
  have h₂ : even (succ n), from even_succ_of_odd h₁,
  absurd h₂ (not_even_of_odd h))

lemma odd_of_even_succ : ∀ {n}, even (succ n) → odd n :=
λ n h, by_contradiction (λ he,
  have h₁ : even n, from even_of_not_odd he,
  have h₂ : odd (succ n), from odd_succ_of_even h₁,
  absurd h (not_even_of_odd h₂))

lemma even_of_even_succ_succ : ∀ {n}, even (succ (succ n)) → even n :=
λ n h, even_of_odd_succ (odd_of_even_succ h)

lemma odd_of_odd_succ_succ : ∀ {n}, odd (succ (succ n)) → odd n :=
λ n h, odd_of_even_succ (even_of_odd_succ h)

lemma even_or_odd : ∀ n, even n ∨ odd n
| 0        := or.inl even_zero
| (succ n) := or.elim (even_or_odd n)
  (λ h : even n, or.inr (odd_succ_of_even h))
  (λ h : odd n,  or.inl (even_succ_of_odd h))

lemma exists_of_even : ∀ {n}, even n → ∃ k, n = 2*k
| 0     h := exists.intro 0 rfl
| 1     h := absurd h not_even_one
| (n+2) h :=
  obtain k (hk : n = 2*k), from exists_of_even (even_of_even_succ_succ h),
  begin existsi (k+1), subst n end

lemma exists_of_odd : ∀ {n}, odd n → ∃ k, n = 2*k + 1
| 0     h := absurd h not_odd_zero
| 1     h := exists.intro 0 rfl
| (n+2) h :=
  obtain k (hk : n = 2*k+1), from exists_of_odd (odd_of_odd_succ_succ h),
  begin existsi (k+1), subst n end

lemma even_of_exists : ∀ {n}, (∃ k, n = 2 * k) → even n
| 0     h := even_zero
| 1     h :=
  obtain k (hk : 1 = 2 * k), from h,
  assert h₁ : 1 mod 2 = (2*k) mod 2, by rewrite hk,
  begin rewrite mul_mod_right at h₁, contradiction end
| (n+2) h :=
  obtain k (hk : n + 2 = 2*k), from h,
  have hk₁ : n = 2*(k - 1), from calc
      n = 2*k - 2   : eq_sub_of_add_eq hk
    ... = 2*(k - 1) : by rewrite mul_sub_left_distrib,
  have ih : even n, from even_of_exists (exists.intro (k-1) hk₁),
  even_succ_succ_of_even ih

lemma odd_of_exists {n} : (∃ k, n = 2 * k + 1) → odd n :=
λ h, by_contradiction (λ hn,
  have h₁ : even n, from even_of_not_odd hn,
  have h₂ : ∃ k, n = 2 * k, from exists_of_even h₁,
  obtain k₁ (hk₁ : n = 2 * k₁ + 1), from h,
  obtain k₂ (hk₂ : n = 2 * k₂), from h₂,
  assert h₃ : (2 * k₁ + 1) mod 2 = (2 * k₂) mod 2, by rewrite [-hk₁, -hk₂],
  begin
    rewrite [mul_mod_right at h₃, add.comm at h₃, add_mul_mod_self_left at h₃],
    contradiction
  end)

lemma even_add_of_even_of_even {n m} : even n → even m → even (n+m) :=
λ h₁ h₂,
obtain k₁ (hk₁ : n = 2 * k₁), from exists_of_even h₁,
obtain k₂ (hk₂ : m = 2 * k₂), from exists_of_even h₂,
even_of_exists (exists.intro (k₁+k₂) (by rewrite [hk₁, hk₂, mul.left_distrib]))

lemma even_add_of_odd_of_odd {n m} : odd n → odd m → even (n+m) :=
λ h₁ h₂,
  assert h₃ : even (succ n + succ m), from even_add_of_even_of_even (even_succ_of_odd h₁) (even_succ_of_odd h₂),
  have h₄ : even(succ (succ (n + m))), by rewrite [add_succ at h₃, succ_add at h₃]; exact h₃,
  even_of_even_succ_succ h₄

lemma odd_add_of_even_of_odd {n m} : even n → odd m → odd (n+m) :=
λ h₁ h₂,
  assert h₃ : even (n + succ m), from even_add_of_even_of_even h₁ (even_succ_of_odd h₂),
  odd_of_even_succ h₃

lemma odd_add_of_odd_of_even {n m} : odd n → even m → odd (n+m) :=
λ h₁ h₂,
  assert h₃ : odd (m+n), from odd_add_of_even_of_odd h₂ h₁,
  by rewrite add.comm at h₃; exact h₃

lemma even_mul_of_even_left {n} (m) : even n → even (n*m) :=
λ h,
  obtain k (hk : n = 2*k), from exists_of_even h,
  even_of_exists (exists.intro (k*m) (by rewrite [hk, mul.assoc]))

lemma even_mul_of_even_right {n} (m) : even n → even (m*n) :=
λ h₁,
  assert h₂ : even (n*m), from even_mul_of_even_left _ h₁,
  by rewrite mul.comm at h₂; exact h₂

lemma odd_mul_of_odd_of_odd {n m} : odd n → odd m → odd (n*m) :=
λ h₁ h₂,
  assert h₃ : even (n * succ m), from even_mul_of_even_right _ (even_succ_of_odd h₂),
  assert h₄ : even (n * m + n), by rewrite mul_succ at h₃; exact h₃,
  by_contradiction (λ hn,
    assert h₅ : even (n*m), from even_of_not_odd hn,
    absurd h₄ (not_even_of_odd (odd_add_of_even_of_odd h₅ h₁)))
end nat
