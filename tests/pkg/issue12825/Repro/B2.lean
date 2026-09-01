module

import all Repro.A

theorem bar : a () ≠ 1 := by
  fun_cases a with simp
