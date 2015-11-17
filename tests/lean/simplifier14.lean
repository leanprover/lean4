-- Basic fusion
import algebra.simplifier
open algebra

universe l
constants (T : Type.{l}) (s : algebra.comm_ring T)
constants (x1 x2 x3 x4 : T) (f g : T → T)
attribute s [instance]
set_option simplify.max_steps 50000
set_option simplify.fuse true

#simplify eq simplifier.som 0 x1
#simplify eq simplifier.som 0 x1 + x1
#simplify eq simplifier.som 0 (x1 + x1) + x1
#simplify eq simplifier.som 0 (x1 + x1) + (x1 + x1)
#simplify eq simplifier.som 0 x1 + x1 + x1 + x1
#simplify eq simplifier.som 0 x1 + x1 + (x1 + x1) + x1
#simplify eq simplifier.som 0 x1 - x1
#simplify eq simplifier.som 0 (x1 - x1) + x1
#simplify eq simplifier.som 0 (x1 + x1) - (x1 + x1)
#simplify eq simplifier.som 0 x1 + x1 - x1 - x1
#simplify eq simplifier.som 0 x1 + x1 + (x1 + x1) + x1
#simplify eq simplifier.som 0 (x1 - x2) + x2 - x1
#simplify eq simplifier.som 0 (x1 + x1 + x2 + x1) - 2* x2 + 1 * x2 - 3 * x1
#simplify eq simplifier.som 0 x2 + x1 - x2 - - x1
#simplify eq simplifier.som 0 (x1 - 2 * x3 * x2) + x2 * x3 * 3 - 1 * 0 * x1 * x2
#simplify eq simplifier.som 0 x2 + x1 - x2 - (- x1)
