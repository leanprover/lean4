example (P : Prop) : ∀ {p : P}, P := by
  exact fun {p} => p

example (P : Prop) : ∀ {p : P}, P := by
  intro h; exact h

example (P : Prop) : ∀ {p : P}, P := by
  exact @id _

example (P : Prop) : ∀ {p : P}, P := by
  exact no_implicit_lambda% id

macro "exact'" x:term : tactic => `(tactic| exact no_implicit_lambda% $x)

example (P : Prop) : ∀ {p : P}, P := by
  exact' id

example (P : Prop) : ∀ {p : P}, P := by
  apply id

example (P : Prop) : ∀ p : P, P := by
  have : _ := 1
  apply id

example (P : Prop) : ∀ {p : P}, P := by
  refine no_implicit_lambda% (have : _ := 1; ?_)
  apply id

example (P : Prop) : ∀ {p : P}, P := by
  have : _ := 1
  apply id
