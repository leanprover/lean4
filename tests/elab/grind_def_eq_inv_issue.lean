namespace Sigma
def map (f₁ : α₁ → α₂) (f₂ : ∀ a, β₁ a → β₂ (f₁ a)) (x : Sigma β₁) : Sigma β₂ :=
  ⟨f₁ x.1, f₂ x.1 x.2⟩

end Sigma

public section

namespace List

variable {α : Type} {α' : Type} {β : α → Type} {β' : α' → Type} {l l₁ l₂ : List (Sigma β)}

opaque keys : List (Sigma β) → List α

variable [DecidableEq α] [DecidableEq α']

/--
error: `grind` failed
case grind
α : Type
β β' : α → Type
f : (a : α) → β a → β' a
head : (a : α) × β a
tail : List ((a : α) × β a)
tail_ih : (map (Sigma.map id f) tail).keys = tail.keys
h : ¬(map (Sigma.map id f) (head :: tail)).keys = (head :: tail).keys
⊢ False
-/
#guard_msgs in
set_option grind.debug true in
omit [DecidableEq α] in
theorem map₂_keys {β β' : α → Type} (f : (a : α) → β a → β' a) (l : List (Σ a, β a)) :
    (l.map (.map id f)).keys = l.keys := by
  induction l
  · sorry
  · grind -verbose [Sigma.map]
