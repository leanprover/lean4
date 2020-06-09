import Lean
new_frontend
open Lean

macro:10000 x:term "ⁿ" : term => `($x ^ $(mkTermId `n))
#check fun (n : Nat) => nⁿ
