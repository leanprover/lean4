-- https://github.com/leanprover/lean4/issues/3805

variable {x y: Nat} {p : Nat → Nat → Prop}
theorem foo (h: ¬ y < x) : p x y := sorry

example (h : x < y): p x y := by simp (discharger := omega) only [foo]
