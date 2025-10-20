import Lean.PremiseSelection.MePo
import Std

set_premise_selector Lean.PremiseSelection.mepoSelector (useRarity := false)

example (a b : Int) : a + b = b + a := by
  suggest_premises
  sorry

-- #time
example (x y z : List Int) : x ++ y ++ z = x ++ (y ++ z) := by
  suggest_premises
  sorry

set_premise_selector Lean.PremiseSelection.mepoSelector (useRarity := true)

example (a b : Int) : a + b = b + a := by
  suggest_premises
  sorry

-- #time
example (x y z : List Int) : x ++ y ++ z = x ++ (y ++ z) := by
  suggest_premises
  sorry

example (x : Std.HashMap Nat Nat) : (x.insert 1 2).erase 1 = x.erase 1 := by
  suggest_premises
  sorry
