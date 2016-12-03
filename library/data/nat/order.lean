/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad

The order relation on the natural numbers.

This is a minimal port of functions from the lean2 library.
-/

import algebra.order

namespace nat

/- min -/

theorem zero_min (a : ℕ) : min 0 a = 0 := min_eq_left (zero_le a)

theorem min_zero (a : ℕ) : min a 0 = 0 := min_eq_right (zero_le a)

-- Distribute succ over min
theorem min_succ_succ (x y : ℕ) : min (succ x) (succ y) = succ (min x y) :=
  let f : x ≤ y → min (succ x) (succ y) = succ (min x y) := λp,
          calc min (succ x) (succ y)
                     = succ x         : if_pos (succ_le_succ p)
                 ... = succ (min x y) : congr_arg succ (eq.symm (if_pos p)) in
  let g : ¬ (x ≤ y) → min (succ x) (succ y) = succ (min x y) := λp,
          calc min (succ x) (succ y)
                     = succ y         : if_neg (λeq, p (pred_le_pred eq))
                 ... = succ (min x y) : congr_arg succ (eq.symm (if_neg p)) in
  decidable.by_cases f g

end nat
