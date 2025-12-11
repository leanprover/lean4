module
/-! Test for E-matching patterns containing nested universe polymorphic ground patterns. -/
example : Id.run (pure true) = true := by
  grind only [Id.run_pure]
