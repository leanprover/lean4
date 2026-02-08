import Lean

open Lean

macro:10000 x:term "ⁿ" : term => `($x ^ $(mkIdent `n))
/-- info: fun n => n ^ n : Nat → Nat -/
#guard_msgs in
#check fun (n : Nat) => nⁿ
