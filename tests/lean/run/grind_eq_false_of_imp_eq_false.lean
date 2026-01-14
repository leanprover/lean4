module
reset_grind_attrs%
open List

attribute [grind] List.map_nil

theorem map_eq_cons_iff {f : α → β} {l : List α} :
    map f l = b :: l₂ ↔ ∃ a l₁, l = a :: l₁ ∧ f a = b ∧ map f l₁ = l₂ := by
  cases l
  case nil => grind
  case cons a l => sorry
