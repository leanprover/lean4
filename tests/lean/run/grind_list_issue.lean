reset_grind_attrs%
set_option grind.warning false
open List Nat

attribute [grind] List.filter_nil List.filter_cons
attribute [grind] List.any_nil List.any_cons

theorem any_filter {l : List α} {p q : α → Bool} :
    (filter p l).any q = l.any fun a => p a && q a := by
  induction l <;> grind

attribute [grind] List.map_nil List.map_cons
attribute [grind] List.all_nil List.all_cons

theorem any_map {l : List α} {p : β → Bool} : (l.map f).any p = l.any (p ∘ f) := by
  induction l <;> grind

theorem all_map {l : List α} {p : β → Bool} : (l.map f).all p = l.all (p ∘ f) := by
  induction l <;> grind
