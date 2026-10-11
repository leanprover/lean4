public section

namespace List

set_option grind.debug true in
theorem take_eq_self_iff (x : List α) {n : Nat} : x.take n = x → x.length ≤ n := by
  grind
