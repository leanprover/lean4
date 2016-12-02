/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

This is a minimal port of functions from the lean2 library.
-/
import algebra.order

namespace nat

  /- sub theorems -/

  theorem succ_sub_succ : Π (n m : ℕ), succ n - succ m = n - m
  | n 0 := rfl
  | n (succ m) :=  congr_arg pred (succ_sub_succ n m)

  theorem sub_add_cancel : Π{n i : ℕ}, i ≤ n → (n - i) + i = n
  | n 0 p := rfl
  | (succ n) (succ i) p :=
    calc (succ n - succ i) + succ i
                      = ((n - i) + succ i) : congr_arg (λ v, v + succ i) (succ_sub_succ n i)
                  ... = succ n             : congr_arg succ (sub_add_cancel (pred_le_pred p))

  /- min -/

  theorem min_zero_left (a : ℕ) : min 0 a = 0 := min_eq_left (zero_le a)

  theorem min_zero_right (a : ℕ) : min a 0 = 0 := min_eq_right (zero_le a)

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
