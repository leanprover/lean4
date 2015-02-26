import data.prod data.unit
open prod

inductive tree (A : Type) : Type :=
| node : A → forest A → tree A
with forest : Type :=
| nil  : forest A
| cons : tree A → forest A → forest A

namespace solution1

inductive tree_forest (A : Type) :=
| of_tree   : tree A   → tree_forest A
| of_forest : forest A → tree_forest A

inductive same_kind {A : Type} : tree_forest A → tree_forest A → Type :=
| is_tree   : Π (t₁ t₂ : tree A),   same_kind (tree_forest.of_tree t₁)   (tree_forest.of_tree t₂)
| is_forest : Π (f₁ f₂ : forest A), same_kind (tree_forest.of_forest f₁) (tree_forest.of_forest f₂)

definition to_tree {A : Type} (tf : tree_forest A) (t : tree A) : same_kind tf (tree_forest.of_tree t) → tree A :=
tree_forest.cases_on tf
  (λ t₁ H, t₁)
  (λ f₁ H, by cases H)

end solution1

namespace solution2

variables {A B : Type}

inductive same_kind : sum A B → sum A B → Prop :=
| isl : Π (a₁ a₂ : A), same_kind (sum.inl a₁) (sum.inl a₂)
| isr : Π (b₁ b₂ : B), same_kind (sum.inr b₁) (sum.inr b₂)

definition to_left (s : sum A B) (a : A) : same_kind s (sum.inl a) → A :=
sum.cases_on s
  (λ a₁ H, a₁)
  (λ b₁ H, false.rec _ (by cases H))

definition to_right (s : sum A B) (b : B) : same_kind s (sum.inr b) → B :=
sum.cases_on s
  (λ a₁ H, false.rec _ (by cases H))
  (λ b₁ H, b₁)

theorem to_left_inl (a₁ a₂ : A) (H : same_kind (sum.intro_left B a₁) (sum.inl a₂)) : to_left (sum.inl a₁) a₂ H = a₁ :=
rfl

theorem to_right_inr (b₁ b₂ : B) (H : same_kind (sum.intro_right A b₁) (sum.inr b₂)) : to_right (sum.inr b₁) b₂ H = b₁ :=
rfl

end solution2
