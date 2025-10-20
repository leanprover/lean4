import Lean.PremiseSelection.MePo

set_premise_selector Lean.PremiseSelection.mepoSelector (useRarity := false)

example (a b : Int) : a + b = b + a := by
  suggest_premises
  sorry

-- #time
example (x y z : List Int) : x ++ y ++ z = x ++ (y ++ z) := by
  suggest_premises
  sorry

-- `useRarity` is too slow in practice: it requires analyzing all the types in the environment.
-- It would need to be cached.

open Lean
run_meta do
  let env ← getEnv
  let i := Lean.PremiseSelection.MePo.symbolFrequency env ``Name
  logInfo m!"{i}"

run_meta do
  let env ← getEnv
  let n := Lean.PremiseSelection.MePo.symbolFrequencyExt.getState env |>.map fun as => as.size
  logInfo m!"{n}"

set_premise_selector Lean.PremiseSelection.mepoSelector (useRarity := true)

example (a b : Int) : a + b = b + a := by
  suggest_premises
  sorry

-- #time
-- example (x y z : List Int) : x ++ y ++ z = x ++ (y ++ z) := by
--   suggest_premises
--   sorry
