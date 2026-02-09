/-!
  Generalize should not try to abstract the variable from hypotheses that are
  implementation details. -/

/-!
  In this case, generalize tries to revert the lemma being defined to generalize
  the 0 in it. -/

example : 0 = 0 → True := by
  intro H; generalize _H : 0 = z at *
  trace_state
  constructor
