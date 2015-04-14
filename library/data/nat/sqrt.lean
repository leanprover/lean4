/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.nat.sqrt
Authors: Leonardo de Moura

Very simple (sqrt n) function that returns s s.t.
    s*s ≤ n ≤ s*s + s + s
-/
import data.nat.order data.nat.sub

namespace nat
open decidable

-- This is the simplest possible function that just performs a linear search
definition sqrt_aux : nat → nat → nat
| 0        n := 0
| (succ s) n := if (succ s)*(succ s) ≤ n then succ s else sqrt_aux s n

theorem sqrt_aux_suc_of_pos {s n} : (succ s)*(succ s) ≤ n → sqrt_aux (succ s) n = (succ s) :=
assume h, if_pos h

theorem sqrt_aux_suc_of_neg {s n} : ¬ (succ s)*(succ s) ≤ n → sqrt_aux (succ s) n = sqrt_aux s n :=
assume h, if_neg h

definition sqrt (n : nat) : nat :=
sqrt_aux n n

theorem sqrt_aux_lower : ∀ {s n : nat}, s ≤ n → sqrt_aux s n * sqrt_aux s n ≤ n
| 0        n h := h
| (succ s) n h := by_cases
  (λ h₁ : (succ s)*(succ s) ≤ n,   by rewrite [sqrt_aux_suc_of_pos h₁]; exact h₁)
  (λ h₂ : ¬ (succ s)*(succ s) ≤ n,
     assert aux : s ≤ n, from lt.step (lt_of_succ_le h),
     by rewrite [sqrt_aux_suc_of_neg h₂]; exact (sqrt_aux_lower aux))

theorem sqrt_lower (n : nat) : sqrt n * sqrt n ≤ n :=
sqrt_aux_lower (le.refl n)

theorem sqrt_aux_upper : ∀ {s n : nat}, n ≤ s*s + s + s → n ≤ sqrt_aux s n * sqrt_aux s n + sqrt_aux s n + sqrt_aux s n
| 0         n   h := h
| (succ s)  n   h := by_cases
  (λ h₁ : (succ s)*(succ s) ≤ n,
    by rewrite [sqrt_aux_suc_of_pos h₁]; exact h)
  (λ h₂ : ¬ (succ s)*(succ s) ≤ n,
    assert h₃ : n < (succ s) * (succ s), from lt_of_not_le h₂,
    assert h₄ : n ≤ s * s + s + s, by rewrite [succ_mul_succ_eq at h₃]; exact h₃,
    by rewrite [sqrt_aux_suc_of_neg h₂]; exact (sqrt_aux_upper h₄))

theorem sqrt_upper (n : nat) : n ≤ sqrt n * sqrt n + sqrt n + sqrt n :=
have aux : n ≤ n*n + n + n, from le_add_of_le_right (le_add_of_le_left (le.refl n)),
sqrt_aux_upper aux

theorem sqrt_aux_eq : ∀ n, sqrt_aux n (n*n) = n
| 0        := rfl
| (succ n) := if_pos !le.refl
end nat
