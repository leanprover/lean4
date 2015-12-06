-- Basic fusion
import algebra.ring

universe l
constants (T : Type.{l}) (s : comm_ring T)
constants (x1 x2 x3 x4 : T) (f g : T → T)
attribute s [instance]
set_option simplify.max_steps 50000
set_option simplify.fuse true

open simplifier.unit simplifier.ac simplifier.neg

#simplify eq env 0 x1
#simplify eq env 0 x1 + x1
#simplify eq env 0 (x1 + x1) + x1
#simplify eq env 0 (x1 + x1) + (x1 + x1)
#simplify eq env 0 x1 + x1 + x1 + x1
#simplify eq env 0 x1 + x1 + (x1 + x1) + x1
#simplify eq env 0 x1 - x1
#simplify eq env 0 (x1 - x1) + x1
#simplify eq env 0 (x1 + x1) - (x1 + x1)
#simplify eq env 0 x1 + x1 - x1 - x1
#simplify eq env 0 x1 + x1 + (x1 + x1) + x1
#simplify eq env 0 (x1 - x2) + x2 - x1
#simplify eq env 0 (x1 + x1 + x2 + x1) - 2* x2 + 1 * x2 - 3 * x1
#simplify eq env 0 x2 + x1 - x2 - - x1
#simplify eq env 0 (x1 - 2 * x3 * x2) + x2 * x3 * 3 - 1 * 0 * x1 * x2
#simplify eq env 0 x2 + x1 - x2 - (- x1)
