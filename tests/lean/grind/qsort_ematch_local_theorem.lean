set_option grind.warning false

namespace Array

private theorem getElem_qpartition_snd_of_lt_lo {n} (lt : α → α → Bool) (as : Vector α n) (lo hi : Nat)
    (hlo : lo < n) (hhi : hi < n) (w : lo ≤ hi)
    (k : Nat) (h : k < lo) : (qpartition as lt lo hi hlo hhi).2[k] = as[k] := sorry

-- First version, works fine:
private theorem getElem_qsort_sort_of_lt_lo
    {n} (lt : α → α → Bool) (as : Vector α n) (lo hi : Nat)
    (hlo : lo < n) (hhi : hi < n) (w : lo ≤ hi)
    (i : Nat) (h : i < lo) : (qsort.sort lt as lo hi hlo hhi)[i] = as[i] := by
  fun_induction qsort.sort
  case case1 a b => sorry
  case case2 a b ih1 ih2 ih3 =>
    unfold qsort.sort
    grind [getElem_qpartition_snd_of_lt_lo]
  case case3 => sorry

-- But this version fails:
private theorem getElem_qsort_sort_of_lt_lo'
    {n} (lt : α → α → Bool) (as : Vector α n) (lo hi : Nat)
    (hlo : lo < n) (hhi : hi < n) (w : lo ≤ hi)
    (i : Nat) (h : i < lo) : (qsort.sort lt as lo hi hlo hhi)[i] = as[i] := by
  fun_induction qsort.sort
  case case1 a b => sorry
  case case2 a b ih1 ih2 ih3 =>
    unfold qsort.sort
    -- Grind can finish from here if we comment out the `simp only`.
    -- But if we do a manual step, then `grind` fails and
    -- we get "failed to create E-match local theorem" issues
    simp only [↓reduceDIte, *]
    grind [getElem_qpartition_snd_of_lt_lo]
  case case3 => sorry
