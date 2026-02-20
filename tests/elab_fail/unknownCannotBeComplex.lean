import Lean

example : Option String := sorry
example : Maybe String := sorry
example : Result String Nat := sorry
example : Nonsense String Nat := sorry
example : MetaM String := sorry

set_option relaxedAutoImplicit false in
example : MetaM String := sorry

set_option relaxedAutoImplicit false in
example : Nonsense String := sorry

example (h₁ : α = β) (as : List α) (P : List β → Type) : P (h₁ ▸ as) := sorry
example {α β h} (h₁ : α = β) (as : List α) (P : List β → Type) : P (h ▸ as) := sorry
example  (h₁ : α = β) (as : List α) (P : List β → Type) : P (h ▸ as) := sorry
set_option relaxedAutoImplicit false in
example (h₁ : α = β) (as : List α) (P : List β → Type) : P (hi ▸ as) := sorry
