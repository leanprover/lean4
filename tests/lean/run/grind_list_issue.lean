reset_grind_attrs%
open List Nat

attribute [grind] List.filter_nil List.filter_cons
attribute [grind] List.any_nil List.any_cons

@[simp] theorem any_filter {l : List α} {p q : α → Bool} :
    (filter p l).any q = l.any fun a => p a && q a := by
  induction l <;> grind
