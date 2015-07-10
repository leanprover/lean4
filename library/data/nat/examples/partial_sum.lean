/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import data.nat
open nat

definition partial_sum : nat → nat
| 0        := 0
| (succ n) := succ n + partial_sum n

example : partial_sum 5 = 15 :=
rfl

example : partial_sum 6 = 21 :=
rfl

lemma two_mul_partial_sum_eq : ∀ n, 2 * partial_sum n = (succ n) * n
| 0        := by reflexivity
| (succ n) := calc
   2 * (succ n + partial_sum n) = 2 * succ n + 2 * partial_sum n  : mul.left_distrib
                   ...   = 2 * succ n + succ n * n  : two_mul_partial_sum_eq
                   ...   = 2 * succ n + n * succ n  : mul.comm
                   ...   = (2 + n) * succ n         : mul.right_distrib
                   ...   = (n + 2) * succ n         : add.comm
                   ...   = (succ (succ n)) * succ n : rfl

theorem partial_sum_eq : ∀ n, partial_sum n = ((n + 1) * n) div 2 :=
take n,
assert h₁ : (2 * partial_sum n) div 2 = ((succ n) * n) div 2, by rewrite two_mul_partial_sum_eq,
assert h₂ : 2 > 0, from dec_trivial,
by rewrite [mul_div_cancel_left _ h₂ at h₁]; exact h₁
