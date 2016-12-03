/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn, Jeremy Avigad
Subtraction on the natural numbers, as well as min, max, and distance.
-/

namespace nat

/- subtraction -/

-- defined in data/nat/sub.lean
protected theorem sub_le_sub_right {n m : ℕ} (H : n ≤ m) : Πk, n - k ≤ m - k
| 0 := H
| (succ z) := pred_le_pred (sub_le_sub_right z)

end nat
