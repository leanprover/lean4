module
open Lean Grind

variable [Field R]

example (M : R) (h₀ : M ≠ 0) {n : Nat} (hn : n > 0) : M ^ n / M = M ^ (n - 1) := by
  cases n <;> grind
