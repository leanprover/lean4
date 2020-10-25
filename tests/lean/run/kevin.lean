import Lean

open Lean

macro:10000 x:term "ⁿ" : term => `($x ^ $(mkIdent `n))
#check fun (n : Nat) => nⁿ
