example [Subsingleton α] (p : α → Prop) : Subsingleton (Subtype p) := by
  constructor
  intro ⟨x, _⟩ ⟨y, _⟩
  have := Subsingleton.elim x y
  subst this
  rfl
