module
reset_grind_attrs%

attribute [grind]
  List.length_cons List.length_nil
  List.getElem_cons
  List.getElem?_cons List.getElem?_nil

example {l : List α} : l[i]? = some a ↔ ∃ h : i < l.length, l[i] = a := by
  induction l generalizing i <;> grind
