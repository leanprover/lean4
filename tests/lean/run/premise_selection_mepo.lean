import Lean.PremiseSelection.MePo

set_premise_selector Lean.PremiseSelection.mepo

example (a b : Int) : a + b = b + a := by
  suggest_premises
  sorry

#time
example (x y z : List Int) : x ++ y ++ z = x ++ (y ++ z) := by
  suggest_premises
  sorry
