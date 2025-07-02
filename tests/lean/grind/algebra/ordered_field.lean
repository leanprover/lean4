variable (ℝ : Type) [Field ℝ] [OrderedRing ℝ]

example (x y : ℝ) (h : x ≠ y) : (x^2 - y^2)/(x - y) = x + y := by grind
example (x y : ℝ) (h : (x + y)^2 ≠ 0) : (x^2 - y^2)/(x + y) = x - y := by grind
example (x y : ℝ) (h : x + y > 1) : (x^2 - y^2)/(x + y) = x - y := by grind
example (x y : ℝ) (_ : x > 1) (_ : y > 1) : (x^2 - y^2)/(x + y) = x - y := by grind
example (x y : ℝ) (_ : x > 1) (_ : y > x^2) : (x^2 - y^2)/(x + y) = x - y := by grind
example (x y : ℝ) (_ : x > 1) (_ : y^3 > x) : (x^2 - y^2)/(x + y) = x - y := by grind
