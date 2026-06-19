module

open List

set_option grind.debug true in
theorem getLast_getLast_eq_getLast_flatten {l : List (List α)}
    (hl : l ≠ []) (hl' : l.getLast hl ≠ []) :
    (l.getLast hl).getLast hl' =
      l.flatten.getLast (flatten_ne_nil_iff.2 ⟨_, getLast_mem hl, hl'⟩) := by
  cases eq_nil_or_concat l with grind
