module
reset_grind_attrs%
attribute [grind] List.length_set
attribute [grind →] List.eq_nil_of_length_eq_zero
attribute [grind] List.getElem_set

open List in
example {as : List α} {i : Nat} (h : i < as.length) :
    as.set i as[i] = as := by
  apply ext_getElem
  · sorry
  · grind

reset_grind_attrs%

opaque P : {n : Nat} → Fin (n+1) → Prop
@[grind] axiom Pax : @P n 0
example (a : Fin 3) : a = 0 → P a := by
  grind
