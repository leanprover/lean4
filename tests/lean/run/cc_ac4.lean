--import data.set.basic
open tactic

constant union_is_assoc {α} : is_associative (set α) (∪)
constant union_is_comm {α} : is_commutative (set α) (∪)
attribute [instance] union_is_assoc union_is_comm

section
  universe variable u
  variables {α : Type u}

  example (a b c d₁ d₂ e₁ e₂ : set α) (f : set α → set α → set α) : b ∪ a = d₁ ∪ d₂ → b ∪ c = e₂ ∪ e₁ → f (a ∪ b ∪ c) (a ∪ b ∪ c) = f (c ∪ d₂ ∪ d₁) (e₂ ∪ a ∪ e₁) :=
  by cc
end
