theorem getElem?_eq_some_iff {l : List α} : l[i]? = some a ↔ ∃ h : i < l.length, l[i] = a := by
  induction l
  · grind
  · cases i
    · -- Better support for implication and dependent implication.
      -- We need inequality propagation (or case-splits)
      grind
    · -- Similarly
      grind

attribute [grind] List.getElem_append_left List.getElem_append_right
attribute [grind] List.length_cons List.length_nil

example {l : List α} {a : α} {i : Nat} (h : i = l.length) (w) :
    (l ++ [a])[i]'w = a := by
  grind -- Similar to issue above.
