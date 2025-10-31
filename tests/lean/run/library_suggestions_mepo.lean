import Lean.LibrarySuggestions.MePo

set_library_suggestions Lean.LibrarySuggestions.mepoSelector (useRarity := false)

example (a b : Int) : a + b = b + a := by
  suggestions
  sorry

example (x y z : List Int) : x ++ y ++ z = x ++ (y ++ z) := by
  suggestions
  sorry

set_library_suggestions Lean.LibrarySuggestions.mepoSelector (useRarity := true)

example (a b : Int) : a + b = b + a := by
  suggestions
  sorry

example (x y z : List Int) : x ++ y ++ z = x ++ (y ++ z) := by
  suggestions
  sorry
