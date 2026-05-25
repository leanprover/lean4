import Init.Data.List.ToArray

example {as bs : List Nat} : as.toArray = bs.toArray ↔ as = bs := by
  simp

example {as bs : List Nat} (h : as.toArray = bs.toArray) : as = bs :=
  List.toArray_eq_toArray_iff.mp h

example {as bs : List Nat} (h : as = bs) : as.toArray = bs.toArray :=
  List.toArray_eq_toArray_iff.mpr h

example {as bs : List Nat} (h : as.toArray = bs.toArray) : as = bs :=
  List.toArray_inj h
