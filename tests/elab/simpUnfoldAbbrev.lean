example {x y : Nat} (h : y > x) : x < y := by
  -- simp should unfold `>` when inserting into the discrimination tree
  simp [h]

abbrev good (n : Nat) :=
  n > 42

example (h : good n) : n > 42 := by
  -- simp should unfold `good` when inserting into the discrimination tree
  simp [h]

example {x y : Nat} (h : x ≠ y) : x ≠ y := by
  -- ≠ is also an abbreviation
  simp [h]
