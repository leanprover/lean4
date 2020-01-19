import Init.Lean
new_frontend
open Lean

macro x:term "ⁿ":10000 : term => `($x ^ $(mkTermId (mkNameSimple "n")))
#check fun (n : Nat) => nⁿ
