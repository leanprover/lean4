def foo := @id
def bar := @id
theorem foo_eq {α} (x : α) : foo x = bar x := rfl
example {p : Nat → Prop} {x} (h : x = bar 1) : p x := by
  simp [*, ← foo_eq]
  show p (foo 1)
  admit
