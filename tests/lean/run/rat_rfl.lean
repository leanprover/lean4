import data.rat
open rat

attribute rat.of_int [coercion]

example : 1 + 2⁻¹ + 3 = 3 + 2⁻¹ + 1⁻¹ :=
rfl
