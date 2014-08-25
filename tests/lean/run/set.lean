import logic
using bool

definition set {{T : Type}} := T → bool
infix `∈`:50 := λx A, A x = tt

check 1 ∈ (λ x, tt)