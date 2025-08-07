module

import Init.Data.Order.Factories

open Std

variable {α : Type u}

section

instance packageOfLE [LE α] [DecidableLE α] [Refl (α := α) (· ≤ ·)]
    [Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·)] : PreorderPackage α := .ofLE α

example [i : LE α] [DecidableLE α] [Refl (α := α) (· ≤ ·)]
    [Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·)] :
    i = (inferInstanceAs (PreorderPackage α)).toLE := rfl

example [LE α] [DecidableLE α] [Refl (α := α) (· ≤ ·)]
    [Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·)] :
    LawfulOrderLE α := inferInstance

example [LE α] [DecidableLE α] [Refl (α := α) (· ≤ ·)]
    [Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·)] :
    LawfulOrderLT α := inferInstance

end

/--
error: could not synthesize default value for field 'lawful_lt' of 'Std.PreorderPackage.OfLEArgs' using tactics
---
error: Failed to automatically prove that the `OrderData` and `LT` instances are compatible.
α : Type u
inst✝² : LE α
inst✝¹ : DecidableLE α
inst✝ : LT α
⊢ ∀ (a b : α), a < b ↔ a ≤ b ∧ ¬b ≤ a
-/
#guard_msgs in
def packageOfLEOfLT1 [LE α] [DecidableLE α] [LT α] : PreorderPackage α := .ofLE α {
  le_refl := sorry
  le_trans := sorry
}

def packageOfLEOfLT2 [LE α] [DecidableLE α] [LT α] (h : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬ b ≤ a) :
    PreorderPackage α := .ofLE α {
  lawful_lt := h
  le_refl := sorry
  le_trans := sorry
}

section

instance packageOfLT [LT α] : PreorderPackage α := .ofLT α

example [i : LE α] : i = (inferInstanceAs (PreorderPackage α)).toLE := rfl

example [LE α] : LawfulOrderLE α := inferInstance
example [LE α] : LawfulOrderLT α := inferInstance

end
