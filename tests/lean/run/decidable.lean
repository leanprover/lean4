import logic data.unit data.bool
open bool unit decidable

constants a b c : bool
constants u v : unit
set_option pp.implicit true
check if ((a = b) ∧ (b = c) → ¬ (u = v) ∨ (a = c) → (a = c) ↔ a = tt ↔ true) then a else b
