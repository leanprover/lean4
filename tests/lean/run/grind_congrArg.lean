set_option grind.warning false

namespace Array

private theorem getElem_qpartition_snd_of_hi_lt {n} (lt : α → α → Bool) (as : Vector α n) (lo hi : Nat)
    (hlo : lo < n) (hhi : hi < n) (w : lo ≤ hi)
    (k : Nat) (h : hi < k) (h' : k < n) : (qpartition as lt lo hi hlo hhi).2[k] = as[k] := sorry

@[local grind] private theorem getElem_qsort_sort_of_hi_lt
    {n} (lt : α → α → Bool) (as : Vector α n) (lo hi : Nat)
    (hlo : lo < n) (hhi : hi < n) (w : lo ≤ hi)
    (i : Nat) (h : hi < i) (h' : i < n) : (qsort.sort lt as lo hi hlo hhi)[i] = as[i] := by
  fun_induction qsort.sort
  case case1 a b =>
    unfold qsort.sort
    grind [getElem_qpartition_snd_of_hi_lt]
  case case2 a b ih1 ih2 ih3 => sorry
  case case3 => sorry
