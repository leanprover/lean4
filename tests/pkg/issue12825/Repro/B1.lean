module

import all Repro.A

theorem foo : a () ≠ 1 := by
  fun_cases a with simp
