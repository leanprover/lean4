import data.rat
open rat

attribute rat.of_int [coercion]

check (0 : ℚ)
check (rat.of_int 0 : ℚ)

constant f : ℚ → Prop
variable a : nat

check f 0
check f a

set_option pp.coercions true

check f a
