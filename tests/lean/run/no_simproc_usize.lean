example : (10 : USize) + 2 = 12 := by
  fail_if_success simp -- We don't have USize simprocs since operations depend on `System.Platform.numBits`
  sorry
