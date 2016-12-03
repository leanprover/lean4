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

theorem add_sub_cancel_left : Π (n m : ℕ), n + m - n = m
| 0 m := nat.zero_add m
| (succ a) m :=
  calc succ a + m - succ a
            = succ (a + m) - succ a
            : congr_arg (λz, z - succ a) (nat.succ_add a m)
        ... = a + m - a : succ_sub_succ_eq_sub (a+m) a
        ... = m         : add_sub_cancel_left a m

-- defined in data/nat/sub.lean
protected theorem sub_le_sub_right {n m : ℕ} (H : n ≤ m) : Πk, n - k ≤ m - k
| 0 := H
| (succ z) := pred_le_pred (sub_le_sub_right z)

end nat
