/-!
Interactive `grind => seq` and `sym => seq` succeed when initialization already closes the
goal, for example from an inconsistent local context. The tactic sequence is skipped in that
case. Previously the sequence ran on an empty goal list and failed with "No goals to be
solved"; in sym mode the preprocessing additionally overwrote the goal's proof with a fresh
metavariable.
-/

example (h : false = true) : True := by
  grind => finish

example (h : false = true) : True := by
  sym => exact True.intro

example (h : False) : True := by
  grind => finish

example (h : False) : True := by
  sym => exact True.intro
