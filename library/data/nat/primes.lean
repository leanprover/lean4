/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Prime numbers
-/
import data.nat.fact data.nat.bquant data.nat.power logic.identities
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

end nat
