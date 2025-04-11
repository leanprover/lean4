reset_grind_attrs%
set_option grind.warning false
attribute [grind] Vector.getElem_swap_of_ne

example (hi : i < n) (hj : j < i) (hk : k < j) (as : Vector α n) (p : α → Prop) (h : p as[k]) :
    p (as.swap i j)[k] := by
  grind

example (p : Nat → Prop) (h : p j) (h' : ∀ i, i < j → p i) : ∀ i, i < j + 1 → p i := by
  grind

example (p : Nat → Prop) (h : p j) (h' : ∀ i, i < j → p i) : ∀ i, i < j + 1 → p i := by
  grind (splits := 0)
