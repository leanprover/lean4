@[simp] theorem getElem_fin [GetElem Cont Nat Elem Dom] (a : Cont) (i : Fin n) (h : Dom a i) :
    a[i] = a[i.1] := rfl

example (a : Array α) (i : Fin a.size) : a[i] = a[i.1] := by
  simp

example (a : Array α) (i : Fin a.size) : a[i] = a[i.1] := by
  rw [getElem_fin]
