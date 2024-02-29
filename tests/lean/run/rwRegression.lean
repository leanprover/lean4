namespace Array

@[simp] theorem getElem_pop (a : Array α) (i : Nat) (hi : i < a.pop.size) :
    a.pop[i] = a[i]'(Nat.lt_of_lt_of_le (a.size_pop ▸ hi) (Nat.sub_le _ _)) :=
  sorry

theorem ex {as : Array α} (h : i < size as)  (hlt: i < size (pop as)) :
    as[i] = (pop as)[i] := by
  rw [getElem_pop] -- should close the goal, proof should be found by unification
