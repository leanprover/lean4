-- normalizing reducible non-subsingleton instances
import algebra.simplifier
open algebra

universe l
constants (T : Type.{l}) (s : algebra.comm_ring T)
constants (x1 x2 x3 x4 : T) (f g : T → T)
attribute s [instance]

set_option pp.all true

#simplify eq null 0 x1
#simplify eq null 0 x1 + x1
#simplify eq null 0 x1 + x1 + x1
#simplify eq null 0 x1 + x1 + x1 + x1
#simplify eq null 0 x1 + x1 + (x1 + x1) + x1
#simplify eq simplifier.ac 0 x1 + x1 + x1
#simplify eq simplifier.ac 0 x1 + x1 + x1 + x1
#simplify eq simplifier.ac 0 x1 + x1 + (x1 + x1) + x1
