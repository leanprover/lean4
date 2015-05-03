definition s : Type := sorry

example (A : Type) (s : A) : A := by exact s
example (A : Type) : A → A := by intro s; exact s
