import standard unit decidable if
using bool unit decidable

variables a b c : bool
variables u v : unit
set_option pp.implicit true
check if ((a = b) ∧ (b = c) → ¬ (u = v) ∨ (a = c) → (a = c) ↔ a = '1 ↔ true) then a else b
