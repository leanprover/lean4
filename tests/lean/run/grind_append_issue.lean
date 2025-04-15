reset_grind_attrs%
set_option grind.warning false

attribute [grind] List.length_cons List.length_nil List.length_append
attribute [grind] List.nil_append List.getElem_cons
attribute [grind] List.eq_nil_of_length_eq_zero List.getElem_append_right

example {l : List α} {a : α} {i : Nat} (h : i = l.length) (w) :
    (l ++ [a])[i]'w = a := by
  grind
