-- Nested fusion
import algebra.ring
open algebra

universe l
constants (T : Type.{l}) (s : algebra.comm_ring T)
constants (x1 x2 x3 x4 : T) (f g : T → T)
attribute s [instance]
set_option simplify.max_steps 50000
set_option simplify.fuse true

open simplifier.unit simplifier.ac simplifier.neg

#simplify eq env 0 f (x1 * x2 * 3 * 4 - 4 * 3 * x1 * x2) + g (x1 * x2 * 3 * 4 - 4 * 3 * x1 * x2)
