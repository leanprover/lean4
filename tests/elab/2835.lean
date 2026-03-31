@[simp] theorem imp_self' {a : Prop} : (a → a) ↔ True := ⟨fun _ => trivial, fun _ => id⟩

example {P : Prop} : P → P := by simp only [imp_self']

example {α : Prop} {P : α → Prop} {f : ∀ {a}, P a → α} {a : α} : (h : P a) → P (f h) := by
  simp only [imp_self']
