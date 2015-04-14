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

theorem sqrt_aux_succ_of_pos {s n} : (succ s)*(succ s) ≤ n → sqrt_aux (succ s) n = (succ s) :=
assume h, if_pos h

theorem sqrt_aux_succ_of_neg {s n} : ¬ (succ s)*(succ s) ≤ n → sqrt_aux (succ s) n = sqrt_aux s n :=
assume h, if_neg h

theorem sqrt_aux_of_le : ∀ {s n : nat}, s * s ≤ n → sqrt_aux s n = s
| 0        n h := rfl
| (succ s) n h := by rewrite [sqrt_aux_succ_of_pos h]

definition sqrt (n : nat) : nat :=
sqrt_aux n n

theorem sqrt_aux_lower : ∀ {s n : nat}, s ≤ n → sqrt_aux s n * sqrt_aux s n ≤ n
| 0        n h := h
| (succ s) n h := by_cases
  (λ h₁ : (succ s)*(succ s) ≤ n,   by rewrite [sqrt_aux_succ_of_pos h₁]; exact h₁)
  (λ h₂ : ¬ (succ s)*(succ s) ≤ n,
     assert aux : s ≤ n, from lt.step (lt_of_succ_le h),
     by rewrite [sqrt_aux_succ_of_neg h₂]; exact (sqrt_aux_lower aux))

theorem sqrt_lower (n : nat) : sqrt n * sqrt n ≤ n :=
sqrt_aux_lower (le.refl n)

theorem sqrt_aux_upper : ∀ {s n : nat}, n ≤ s*s + s + s → n ≤ sqrt_aux s n * sqrt_aux s n + sqrt_aux s n + sqrt_aux s n
| 0         n   h := h
| (succ s)  n   h := by_cases
  (λ h₁ : (succ s)*(succ s) ≤ n,
    by rewrite [sqrt_aux_succ_of_pos h₁]; exact h)
  (λ h₂ : ¬ (succ s)*(succ s) ≤ n,
    assert h₃ : n < (succ s) * (succ s), from lt_of_not_le h₂,
    assert h₄ : n ≤ s * s + s + s, by rewrite [succ_mul_succ_eq at h₃]; exact h₃,
    by rewrite [sqrt_aux_succ_of_neg h₂]; exact (sqrt_aux_upper h₄))

theorem sqrt_upper (n : nat) : n ≤ sqrt n * sqrt n + sqrt n + sqrt n :=
have aux : n ≤ n*n + n + n, from le_add_of_le_right (le_add_of_le_left (le.refl n)),
sqrt_aux_upper aux

theorem sqrt_aux_eq : ∀ {s n}, s ≥ n → sqrt_aux s (n*n) = n
| 0        n h :=
   assert neqz : n = 0, from eq_zero_of_le_zero h,
   by rewrite neqz
| (succ s) n h := by_cases
  (λ h₁ : (succ s)*(succ s) ≤ n*n,
    assert h₂ : (succ s)*(succ s) ≥ n*n, from mul_le_mul h h,
    assert h₃ : (succ s)*(succ s) = n*n, from le.antisymm h₁ h₂,
    assert h₄ : ¬ succ s > n, from
      assume ssgtn : succ s > n,
        assert h₅ : (succ s)*(succ s) > n*n, from mul_lt_mul_of_le_of_le ssgtn ssgtn,
        have   h₆ : n*n > n*n, by rewrite [h₃ at h₅]; exact h₅,
        absurd h₆ !lt.irrefl,
    have sslen   : succ s ≤ n, from le_of_not_lt h₄,
    assert sseqn : succ s = n, from le.antisymm sslen h,
    by rewrite [sqrt_aux_succ_of_pos h₁]; exact sseqn)
  (λ h₂ : ¬ (succ s)*(succ s) ≤ n*n,
    or.elim (eq_or_lt_of_le h)
      (λ sseqn, by rewrite [sseqn at h₂]; exact (absurd !le.refl h₂))
      (λ sgen : s ≥ n,
        by rewrite [sqrt_aux_succ_of_neg h₂]; exact (sqrt_aux_eq sgen)))

private theorem le_squared : ∀ (n : nat), n ≤ n*n
| 0        := !le.refl
| (succ n) :=
  have   aux₁ : 1 ≤ succ n, from succ_le_succ !zero_le,
  assert aux₂ : 1 * succ n ≤ succ n * succ n, from mul_le_mul aux₁ !le.refl,
  by rewrite [one_mul at aux₂]; exact aux₂

theorem sqrt_eq (n : nat) : sqrt (n*n) = n :=
sqrt_aux_eq !le_squared

theorem mul_square_cancel {a b : nat} : a*a = b*b → a = b :=
assume h,
assert aux : sqrt (a*a) = sqrt (b*b), by rewrite h,
by rewrite [*sqrt_eq at aux]; exact aux
end nat
