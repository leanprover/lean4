
/-!
Test the `rightact%` elaborator for `HPow.hPow`, added to address #2854
-/

open Lean

variable (n : Nat) (m : Int) (q : Rat)

#check n ^ 2 + m ^ 2
#check n ^ 2 + 1
#check (n ^ 2 + 1 : Int)
#check (n ^ 2 + (1 : Nat) : Int)

#check q ^ n + 1
#check q ^ m + 1
#check q ^ (n : Int) + 1

#check 12 * q + 1 ≤ 13 * q ^ 2
#check (12 : Rat) * q + (1 : Rat) ≤ (13 : Rat) * q ^ 2
