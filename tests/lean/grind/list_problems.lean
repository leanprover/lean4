reset_grind_attrs%

attribute [grind] List.getElem_append_left List.getElem_append_right
attribute [grind] List.length_cons List.length_nil

example {l : List α} {a : α} {i : Nat} (h : i = l.length) (w) :
    (l ++ [a])[i]'w = a := by
  grind -- Similar to issue above.

---
