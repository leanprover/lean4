import algebra.ring
open algebra
universe l
constants (A : Type.{l}) (s : comm_ring A) (x : A)
attribute s [instance]

set_option simplify.numerals true

#simplify eq env 0 (1:A)
#simplify eq env 0 (1:A) + 1
#simplify eq env 0 (1:A) + 1 + 1
#simplify eq env 0 (1:A) + 2 + 1
#simplify eq env 0 (1:A) + 2 * 7 + 1
#simplify eq env 0 (1:A) + 2 * 7 + 10
#simplify eq env 0 (10000000000000000000:A) + 10000000000000000000
