import algebra.simplifier
open algebra simplifier.som

set_option simplify.max_steps 1000
universe l
constants (T : Type.{l}) (s : algebra.comm_ring T)
constants (x1 x2 x3 x4 : T) (f g : T → T)
attribute s [instance]

#simplify eq simplifier.som 0 x2 + (1 * g x1 + 0 + (f x3 * 3 * 1 * (x2 + 0 + g x1 * 7) * x2 * 1)) + 5 * (x4 + f x1)
