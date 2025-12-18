import Lean

open Lean Elab

def orderFuzzyMatches (names : Array Name) (pattern : String) : Array Name :=
  names.filterMap (fun n => (n, ·) <$> Lean.FuzzyMatching.fuzzyMatchScoreWithThreshold? pattern n.toString) |>.qsort (·.2 ≥ ·.2) |>.map (·.1)

-- patterns matching at the end of a name should get a bonus
#eval orderFuzzyMatches #[`Array.extract, `Lean.extractMainModule] "extract"
