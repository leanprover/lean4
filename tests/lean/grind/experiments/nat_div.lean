open Nat

grind_pattern div_add_mod => m % n
grind_pattern div_add_mod => m / n

attribute [grind →] Nat.mul_le_of_le_div
