reset_grind_attrs%
set_option grind.warning false

attribute [grind] List.length_set
attribute [grind →] List.eq_nil_of_length_eq_zero
attribute [grind] List.getElem_set

open List in
example {as : List α} {i : Nat} (h : i < as.length) :
    as.set i as[i] = as := by
  apply ext_getElem
  · sorry
  · grind
