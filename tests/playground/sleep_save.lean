macro "expensive_tactic" : tactic => `(sleep 5000)

example (h₁ : x = y) (h₂ : y = z) : z = x := by
  expensive_tactic
  save
  have : y = x := h₁.symm
  have : z = y := h₂.symm
  trace "hello world"
  apply this.trans
  exact ‹y = x›
