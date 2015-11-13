import data.int
open algebra nat int

variables a b c : nat
variables i j : int

set_option pp.notation false
set_option pp.numerals false
set_option pp.implicit true
set_option pp.coercions true

#normalizer a + b
#normalizer (a + b) * c + 1
#normalizer a + i + 15

variables A : Type
variables [s : ring A]
include s
variables x y : A
#normalizer x + y * x
#normalizer x + 3
