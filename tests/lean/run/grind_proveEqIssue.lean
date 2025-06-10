reset_grind_attrs%
open List Nat

attribute [grind] List.getElem_cons_zero

theorem getElem_cons {l : List α} (w : i < (a :: l).length) :
    (a :: l)[i] =
      if h : i = 0 then a else l[i-1]'(match i, h with | i+1, _ => succ_lt_succ_iff.mp w) := by
  split
  · grind
  · sorry
