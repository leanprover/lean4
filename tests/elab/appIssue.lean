instance {α : Type u} {β : Type v} [LE β] : LE (α → β) where
  le f g := ∀ i, f i ≤ g i

class LE_trans (α : Type u) extends LE α where
  le_trans : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c

export LE_trans (le_trans)

instance {α : Type u} {β : Type v} [LE_trans β] : LE_trans (α → β) where
  le_trans h₁ h₂ i :=  le_trans (h₁ i) (h₂ i)

example {α β} [LE_trans β] (x y z : α → β) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
  assumption
  assumption

example {α β} [LE_trans β] (x y z : α → β) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans <;> assumption
