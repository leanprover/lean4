import Std.Tactic.BVDecide

example {α : Type} {x : α} {p : α → Prop} (h1 : ∃ x, p x) (h2 : ∀ x, ¬p x) : False := by
  epr

example {α : Type} {x : α} {p : α → Prop} (h2 : (∀ x, ¬p x) ∧ (∀ x, p x)) : False := by
  epr

example {α : Type} {x : α} {p : α → Prop} (h2 : ∀ x, (∃ y, p y) ∧ ¬ p x) : False := by
  epr

example {α : Type} (a b c d : α) (p : α → Prop) (h1 : ∀ (x : α), x = a ∨ x = b) (h2 : p a ≠ p c) (h5 : p b ≠ p c) : False := by
  epr

