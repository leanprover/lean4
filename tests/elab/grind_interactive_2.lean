import Lean.LibrarySuggestions.Default

theorem sq_inj (x y : Nat) (h : x ^ 2 = y ^ 2) : x = y := by
  -- Puzzle for anyone bored: a quick Mathlib-free proof?
  sorry

example (a b c d e : Nat) (_ : a = b) (_ : b = c) (_ : c ^ 2 = d ^ 2) (_ : d = e) : a = e := by
  grind =>
    -- We can verify that `grind` can see certain facts:
    have : a = c
    -- We can ask for all the known equivalence classes,
    -- or classes involving certain terms:
    show_eqcs a
    -- We can add additional facts, giving proofs inline.
    have : c = d := by grind? +suggestions
    -- These facts are automatically used to extend equivalence classes,
    -- so in this case the `have` statement itself closes the goal.

example (a b c d e : Nat) (_ : a = b) (_ : b = c) (_ : c ^ 2 = d ^ 2) (_ : d = e) : a = e := by
  grind [sq_inj]

example (x y : Rat) (_ : x^2 = 1) (_ : x + y = 1) : y ≤ 2 := by
  fail_if_success grind
  grind =>
    -- We can also use `have` statements as clues to guide `grind`.
    have : x = 1 ∨ x = -1
    -- Here `grind` can both prove the `have` statement (via a Grobner argument)
    -- and finish off afterwards (using linear arithmetic),
    -- even though it can't close the original goal by itself.
    finish
