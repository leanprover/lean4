macro "expensive_tactic" : tactic => `(sleep 5000)

example (h₁ : x = y) (h₂ : y = z) : z = x := by
  expensive_tactic
  save
  have : y = x := h₁.symm
  have : z = y := h₂.symm
  trace "hello world"
  apply this.trans
  exact ‹y = x›

example (h₁ : p ∨ q) (h₂ : p → x = 0) (h₃ : q → y = 0) : x * y = 0 := by
  expensive_tactic
  save
  match h₁ with
  | .inr h =>
    expensive_tactic
    save
    have : y = 0 := h₃ h
    simp [*]
  | .inl h => stop done

example (h₁ : p ∨ q) (h₂ : p → x = 0) (h₃ : q → y = 0) : x * y = 0 := by
  expensive_tactic
  save
  cases h₁ with
  | inr h =>
    expensive_tactic
    save
    have : y = 0 := h₃ h
    simp [*]
  | inl h => stop
    expensive_tactic
    save
    have : x = 0 := h₂ h
    simp [*]
    done
