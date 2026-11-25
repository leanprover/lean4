import Std.Tactic.BVDecide

/-!
Tests for `epr`'s NNF procedure.
-/

example {α : Type} {p : Prop} (h1 : ¬∀ _ : α, p) (h2 : p) : False := by
  epr

example {α : Type} {a : α} {p : Prop} (h : ¬p) : p ↔ ∃ _ : α, p := by
  epr

example {α : Type} {a : α} : false = true ↔ ∃ _ : α, false = true := by
  epr

/-! Negated implications still become conjunctions. -/

example {α : Type} {a : α} {p : Prop} {q : α → Prop} (h1 : ¬(p → ∀ x, q x)) (h2 : ∀ x, q x) :
    False := by
  epr

example {α : Type} {a : α} {p : Prop} {q : α → Prop} (h1 : ¬((∀ x, q x) → p)) (h2 : p) :
    False := by
  epr
