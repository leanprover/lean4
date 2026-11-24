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

open Classical

example {α : Type} {a : α} {p : α → Prop} (h1 : (!decide (∃ x, p x)) = true) (h2 : p a) :
    False := by
  epr

example {α : Type} {a : α} {p : α → Prop} (h1 : true = (decide (∃ x, p x) == false))
    (h2 : p a) : False := by
  epr

example {α : Type} {a : α} {p : α → Prop} {q : Bool} (h1 : (q || !decide (∃ x, p x)) = true)
    (h2 : q = false) (h3 : p a) : False := by
  epr

example {α : Type} {a : α} {p : α → Prop} (h1 : (decide (∃ x, p x) && true) = false)
    (h2 : p a) : False := by
  epr

example {α : Type} {a : α} {p : α → Prop} (h1 : (decide (∃ x, p x) ^^ true) = true)
    (h2 : p a) : False := by
  epr

example {α : Type} {a : α} {p : α → Prop} (h1 : (decide (∃ x, p x) != false) = false)
    (h2 : p a) : False := by
  epr

example {α : Type} {a : α} {p : α → Prop} {c : Bool}
    (h1 : (bif c then !decide (∃ x, p x) else false) = true) (h2 : p a) : False := by
  epr

example {α : Type} {a : α} {p : α → Prop} {c : Prop} [Decidable c]
    (h1 : (if c then !decide (∃ x, p x) else false) = true) (h2 : p a) : False := by
  epr

example {α : Type} {a : α} {p : α → Prop} (h1 : ¬(decide (∀ x, p x) = false)) (h2 : ¬p a) :
    False := by
  epr
