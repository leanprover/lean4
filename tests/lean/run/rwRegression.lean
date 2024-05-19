namespace Array

theorem ex {as : Array α} (h : i < size as)  (hlt: i < size (pop as)) :
    as[i] = (pop as)[i] := by
  rw [getElem_pop] -- should close the goal, proof should be found by unification
