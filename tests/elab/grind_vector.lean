module

/-!
Tests for `grind` support for vectors, including componentwise algebraic operations.
-/

example [BEq α] (xs ys : Vector α n) : (xs.toList == ys.toList) = (xs == ys) := by grind

example [LT α] {xs ys : Vector α n} : xs.toList < ys.toList ↔ xs < ys := by grind

example (xs ys zs : Vector Nat n) : (xs + ys) + zs = xs + (ys + zs) := by grind

example (xs : Vector Int n) : -xs + xs = 0 := by grind

section

attribute [local instance] Vector.instMul

example (xs ys zs : Vector Nat n) : xs * (ys + zs) = xs * ys + xs * zs := by grind

end

example (c d : Nat) (xs : Vector Nat n) : (c + d) • xs = c • xs + d • xs := by grind

example (c : Nat) (xs ys : Vector Nat n) : c * (xs + ys) = c * xs + c * ys := by grind
