import data.rat
open nat int rat

attribute rat.of_int [coercion]

eval (8 * 6⁻¹) + (1:rat)
