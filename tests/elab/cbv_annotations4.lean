module

public import Init.Data.Array.MinMax

def maxElement (xs : Array Int) : Int :=
  xs.max?.getD 0

example : maxElement #[1, 2, 3] = 3 := by cbv
example : maxElement #[5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10] = 124 := by cbv
