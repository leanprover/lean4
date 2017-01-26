prelude

init_quotient

/- definit eq as the empty type -/
inductive {u} eq {α : Type u} (a : α) : α → Type 0
| refl : ∀ (b : α), eq b

init_quotient
