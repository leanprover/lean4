-- Basic fusion
import algebra.ring algebra.numeral
open algebra

universe l
constants (T : Type.{l}) (s : algebra.comm_ring T)
constants (x1 x2 x3 x4 : T) (f g : T → T)
attribute s [instance]
set_option simplify.max_steps 50000
set_option simplify.fuse true

open simplifier.unit simplifier.ac simplifier.neg

#simplify eq env 0 x1 * x2
#simplify eq env 0 x1 * 2 * x2
#simplify eq env 0 x1 * 2 * x2 * 3
#simplify eq env 0 2 * x2 + x1 * 8 * x2 * 4
#simplify eq env 0 2 * x2 - x1 * 8 * x2 * 4
#simplify eq env 0 2 * x2 - 8 * x2 * 4 * x1
#simplify eq env 0 x2 * x1 + 3 * x1 + (2 * x2 - 8 * x2 * 4 * x1) + x1 * x2
#simplify eq env 0 (x1 * x3 + x1 * 2 + x2 * 3 * x3 + x1 * x2) - 2* x2 * x1 + 1 * x2 * x1 - 3 * x1 * x3
#simplify eq env 0 2 * 2 + x1
#simplify eq env 0 x2 * (2 * 2) + x1
#simplify eq env 0 2 * 2 * x2 + x1
#simplify eq env 0 2 * x2 * 2 + x1
#simplify eq env 0 200 * x2 * 200 + x1
#simplify eq env 0 x1 * 200 * x2 * 200 + x1
#simplify eq env 0 x1 * 200 * x2 * x3 * 200 + x1
#simplify eq env 0 x1 * 200 * x2 * x3 * x4 * 200 + x1
