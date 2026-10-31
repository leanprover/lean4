/-!
`-0 : Int` denotes the same value as `0`, but used to survive normalization as a negative
literal. `grind` then treated the two as distinct interpreted values and closed the goal with a
`decide` proof rejected by the kernel. Reported on Mathlib's `Finset.prod_Icc_succ_eq_mul_endpoints`,
where the cast `((0 : Nat) : Int)` reduces to `0` under a negation.
-/

example (f : Int → Int) : f (-((0 : Nat) : Int)) = f 0 := by grind
example (f : Int → Int) : f (-(0 : Int)) = f 0 := by grind
example (f : Int → Int) (h : f 0 = 1) : f (-((0 : Nat) : Int)) = 1 := by grind
example (x : Int) (h : x = -0) : x = 0 := by grind
example (f : Int → Int) (h : f (-0) ≠ f 0) : False := by grind

-- The simproc normalizes `-0` to `0`
example : (-(0 : Int)) = 0 := by simp only [Int.reduceNeg]
example (f : Int → Int) : f (-0) = f 0 := by simp only [Int.reduceNeg]
