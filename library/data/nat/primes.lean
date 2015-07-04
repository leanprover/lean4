/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Prime numbers
-/
import data.nat.fact data.nat.gcd data.nat.bquant data.nat.power data.nat.parity logic.identities
open bool

namespace nat
open decidable

definition prime [reducible] (p : nat) := p ≥ 2 ∧ ∀ m, m ∣ p → m = 1 ∨ m = p

definition prime_ext (p : nat) := p ≥ 2 ∧ ∀ m, m ≤ p → m ∣ p → m = 1 ∨ m = p
local attribute prime_ext [reducible]

lemma prime_ext_iff_prime (p : nat) : prime_ext p ↔ prime p :=
iff.intro
  begin
    intro h, cases h with h₁ h₂, constructor, assumption,
    intro m d, exact h₂ m (le_of_dvd (lt_of_succ_le (le_of_succ_le h₁)) d) d
  end
  begin
    intro h, cases h with h₁ h₂, constructor, assumption,
    intro m l d, exact h₂ m d
  end

definition decidable_prime [instance] (p : nat) : decidable (prime p) :=
decidable_of_decidable_of_iff _ (prime_ext_iff_prime p)

lemma ge_two_of_prime {p : nat} : prime p → p ≥ 2 :=
assume h, obtain h₁ h₂, from h, h₁

lemma not_prime_zero : ¬ prime 0 :=
λ h, absurd (ge_two_of_prime h) dec_trivial

lemma not_prime_one : ¬ prime 1 :=
λ h, absurd (ge_two_of_prime h) dec_trivial

lemma prime_two : prime 2 :=
dec_trivial

lemma prime_three : prime 3 :=
dec_trivial

lemma pred_prime_pos {p : nat} : prime p → pred p > 0 :=
assume h,
have h₁ : p ≥ 2, from ge_two_of_prime h,
lt_of_succ_le (pred_le_pred h₁)

lemma succ_pred_prime {p : nat} : prime p → succ (pred p) = p :=
assume h, succ_pred_of_pos (lt_of_succ_le (le_of_succ_le (ge_two_of_prime h)))

lemma divisor_of_prime {p m : nat} : prime p → m ∣ p → m = 1 ∨ m = p :=
assume h d, obtain h₁ h₂, from h, h₂ m d

lemma gt_one_of_pos_of_prime_dvd {i p : nat} : prime p → 0 < i → i mod p = 0 → 1 < i :=
assume ipp pos h,
have h₁ : p ∣ i, from dvd_of_mod_eq_zero h,
have h₂ : p ≥ 2, from ge_two_of_prime ipp,
have h₃ : p ≤ i, from le_of_dvd pos h₁,
lt_of_succ_le (le.trans h₂ h₃)

theorem has_divisor_of_not_prime {n : nat} : n ≥ 2 → ¬ prime n → ∃ m, m ∣ n ∧ m ≠ 1 ∧ m ≠ n :=
assume h₁ h₂,
have h₃ : ¬ prime_ext n, from iff.mp' (not_iff_not_of_iff !prime_ext_iff_prime) h₂,
have h₄ : ¬ n ≥ 2 ∨ ¬ (∀ m, m ≤ n → m ∣ n → m = 1 ∨ m = n), from iff.mp !not_and_iff_not_or_not h₃,
have h₅ : ¬ (∀ m, m ≤ n → m ∣ n → m = 1 ∨ m = n), from or_resolve_right h₄ (not_not_intro h₁),
have h₆ : ¬ (∀ m, m < succ n → m ∣ n → m = 1 ∨ m = n), from
  assume h, absurd (λ m hl hd, h m (lt_succ_of_le hl) hd) h₅,
have h₇ : ∃ m, m < succ n ∧ ¬(m ∣ n → m = 1 ∨ m = n), from bex_not_of_not_ball h₆,
obtain m hlt (h₈ : ¬(m ∣ n → m = 1 ∨ m = n)), from h₇,
obtain (h₈ : m ∣ n) (h₉ : ¬ (m = 1 ∨ m = n)), from iff.mp !not_implies_iff_and_not h₈,
have h₁₀ : ¬ m = 1 ∧ ¬ m = n, from iff.mp !not_or_iff_not_and_not h₉,
exists.intro m (and.intro h₈ h₁₀)

theorem has_divisor_of_not_prime2 {n : nat} : n ≥ 2 → ¬ prime n → ∃ m, m ∣ n ∧ m ≥ 2 ∧ m < n :=
assume h₁ h₂,
have n_ne_0 : n ≠ 0, from assume h, begin subst n, exact absurd h₁ dec_trivial end,
obtain m m_dvd_n m_ne_1 m_ne_n, from has_divisor_of_not_prime h₁ h₂,
assert m_ne_0 : m ≠ 0, from assume h, begin subst m, exact absurd (eq_zero_of_zero_dvd m_dvd_n) n_ne_0 end,
begin
  existsi m, split, assumption,
  split,
    {cases m with m, exact absurd rfl m_ne_0, cases m with m, exact absurd rfl m_ne_1, exact succ_le_succ (succ_le_succ (zero_le _))},
    {have m_le_n : m ≤ n, from le_of_dvd (pos_of_ne_zero n_ne_0) m_dvd_n,
     exact lt_of_le_and_ne m_le_n m_ne_n}
end

theorem has_prime_divisor {n : nat} : n ≥ 2 → ∃ p, prime p ∧ p ∣ n :=
nat.strong_induction_on n
  (take n,
   assume ih : ∀ m, m < n → m ≥ 2 → ∃ p, prime p ∧ p ∣ m,
   assume n_ge_2 : n ≥ 2,
   by_cases
    (λ h : prime n, exists.intro n (and.intro h (dvd.refl n)))
    (λ h : ¬ prime n,
      obtain m m_dvd_n m_ge_2 m_lt_n, from has_divisor_of_not_prime2 n_ge_2 h,
      obtain p (hp : prime p) (p_dvd_m : p ∣ m), from ih m m_lt_n m_ge_2,
      have p_dvd_n : p ∣ n, from dvd.trans p_dvd_m m_dvd_n,
      exists.intro p (and.intro hp p_dvd_n)))

open eq.ops

theorem infinite_primes (n : nat) : ∃ p, p ≥ n ∧ prime p :=
let m := fact (n + 1) in
have Hn1 : n + 1 ≥ 1, from succ_le_succ (zero_le _),
have m_ge_1 : m ≥ 1,  from le_of_lt_succ (succ_lt_succ (fact_gt_0 _)),
have m1_ge_2 : m + 1 ≥ 2, from succ_le_succ m_ge_1,
obtain p (prime_p : prime p) (p_dvd_m1 : p ∣ m + 1), from has_prime_divisor m1_ge_2,
have p_ge_2 : p ≥ 2, from ge_two_of_prime prime_p,
have p_gt_0 : p > 0, from lt_of_succ_lt (lt_of_succ_le p_ge_2),
have p_ge_n : p ≥ n, from by_contradiction
  (assume h₁ : ¬ p ≥ n,
    have h₂ : p < n, from lt_of_not_ge h₁,
    have h₃ : p ≤ n + 1, from le_of_lt (lt.step h₂),
    have h₄ : p ∣ m, from dvd_fact p_gt_0 h₃,
    have h₅ : p ∣ 1, from dvd_of_dvd_add_right (!add.comm ▸ p_dvd_m1) h₄,
    have h₆ : p ≤ 1, from le_of_dvd zero_lt_one h₅,
    absurd (le.trans p_ge_2 h₆) dec_trivial),
exists.intro p (and.intro p_ge_n prime_p)

lemma odd_of_prime {p : nat} : prime p → p > 2 → odd p :=
λ h₁ h₂, by_contradiction (λ hn,
  have he : even p, from even_of_not_odd hn,
  obtain k (hk : p = 2*k), from exists_of_even he,
  have h₂ : 2 ∣ p, by rewrite [hk]; apply dvd_mul_right,
  or.elim (divisor_of_prime h₁ h₂)
    (λ h : 2 = 1, absurd h dec_trivial)
    (λ h : 2 = p, by subst h; exact absurd h₂ !lt.irrefl))

lemma coprime_of_prime_of_not_dvd {p n : nat} : prime p → ¬ p ∣ n → coprime p n :=
λ h₁ h₂,
  assert d₁ : gcd p n ∣ p, from !gcd_dvd_left,
  assert d₂ : gcd p n ∣ n, from !gcd_dvd_right,
  or.elim (divisor_of_prime h₁ d₁)
    (λ h : gcd p n = 1, h)
    (λ h : gcd p n = p,
      assert d₃ : p ∣ n, by rewrite -h; exact d₂,
      by contradiction)

lemma dvd_or_dvd_of_prime_of_dvd_mul {p m n : nat} : prime p → p ∣ m * n → p ∣ m ∨ p ∣ n :=
λ h₁ h₂, by_contradiction (λ h,
  obtain (n₁ : ¬ p ∣ m) (n₂ : ¬ p ∣ n), from iff.mp !not_or_iff_not_and_not h,
  assert c₁ : coprime p m, from coprime_of_prime_of_not_dvd h₁ n₁,
  assert n₃ : p ∣ n, from dvd_of_coprime_of_dvd_mul_left c₁ h₂,
  by contradiction)

lemma dvd_of_prime_of_dvd_pow {p m : nat} : ∀ {n}, prime p → p ∣ m^n → p ∣ m
| 0 hp hd :=
  assert h₁ : p = 1, from eq_one_of_dvd_one hd,
  have h₂ : 1 ≥ 2, by rewrite -h₁; apply ge_two_of_prime hp,
  absurd h₂ dec_trivial
| (succ n) hp hd :=
  have hd₁ : p ∣ (m^n)*m, by rewrite [pow_succ at hd]; exact hd,
  or.elim (dvd_or_dvd_of_prime_of_dvd_mul hp hd₁)
    (λ h, dvd_of_prime_of_dvd_pow hp h)
    (λ h, h)

lemma coprime_pow_of_prime_of_not_dvd {p m a : nat} : prime p → ¬ p ∣ a → coprime a (p^m) :=
λ h₁ h₂, coprime_pow_right m (coprime_swap (coprime_of_prime_of_not_dvd h₁ h₂))

lemma coprime_primes {p q : nat} : prime p → prime q → p ≠ q → coprime p q :=
λ hp hq hn,
  assert d₁ : gcd p q ∣ p, from !gcd_dvd_left,
  assert d₂ : gcd p q ∣ q, from !gcd_dvd_right,
  or.elim (divisor_of_prime hp d₁)
    (λ h : gcd p q = 1, h)
    (λ h : gcd p q = p,
      have d₃ : p ∣ q, by rewrite -h; exact d₂,
      or.elim (divisor_of_prime hq d₃)
        (λ h₁ : p = 1, by subst p; exact absurd hp not_prime_one)
        (λ he : p = q, by contradiction))

lemma coprime_pow_primes {p q : nat} (n m : nat) : prime p → prime q → p ≠ q → coprime (p^n) (q^m) :=
λ hp hq hn, coprime_pow_right m (coprime_pow_left n (coprime_primes hp hq hn))

end nat
