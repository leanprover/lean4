import data.vector
open vector nat decidable

variable A : Type

definition foo [H : decidable_eq A] : ∀ {n : nat} (v₁ v₂ : vector A n), decidable (v₁ = v₂)
| ⌞0⌟    []      []      := sorry
| ⌞n+1⌟  (a::v₁) (b::v₂) := sorry
