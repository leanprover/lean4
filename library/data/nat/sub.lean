/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn, Jeremy Avigad
Subtraction on the natural numbers, as well as min, max, and distance.
-/

namespace nat

/- subtraction -/

theorem succ_sub_succ : Π (n m : ℕ), succ n - succ m = n - m
| n 0 := rfl
| n (succ m) :=  congr_arg pred (succ_sub_succ n m)

protected theorem sub_add_cancel : Π{n i : ℕ}, i ≤ n → (n - i) + i = n
| n 0 p := rfl
| (succ n) (succ i) p :=
  calc (succ n - succ i) + succ i
                      = ((n - i) + succ i) : congr_arg (λ v, v + succ i) (succ_sub_succ n i)
                  ... = succ n             : congr_arg succ (sub_add_cancel (pred_le_pred p))

end nat
