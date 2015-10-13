import logic
open bool nat

definition set {{T : Type}} := T → bool
infix `∈` := λx A, A x = tt

check 1 ∈ (λ x : nat, tt)
