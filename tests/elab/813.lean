open Function
theorem constApply {y : β} {x : α} : const α y x = y := rfl
example (p : Nat → Prop) (h : p 1) : p (const Nat 1 2) := by simp only [constApply]; trace_state; exact h -- simplifies
example (p : α → Prop) (h : p a) : p (const Nat a 2) := by simp only [constApply]; trace_state; exact h -- simplifies
example (f : α → α) (p : α → Prop) (h : p (f a)) : p (const Nat (f a) 2) := by simp only [constApply]; trace_state; exact h -- simplifies
