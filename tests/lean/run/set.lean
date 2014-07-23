import standard bool
using bool

definition set {{T : Type}} := T → bool
infix `∈`:50 := λx A, A x = '1

check 1 ∈ (λ x, '1)