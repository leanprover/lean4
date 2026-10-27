/-!
`liaSteps` also bounds the cases of Cooper and disequality splits in `lia`. The next case of a split
can be refuted as soon as it is asserted, so an enumeration of thousands of cases never reached the
step check in the main loop, and the solver could enumerate for minutes, or produce a proof the kernel
rejects, instead of stopping at the threshold.
-/

set_option warn.sorry false
example (x : Int) (h : 0 ≤ x ∧ x < 2 ^ 32) : ((x % 256) * 16777216 + (x / 256 % 256) * 65536 + (x / 65536 % 256) * 256 + x / 16777216) / 65536 % 256 = x / 256 % 256 := by
  fail_if_success lia (liaSteps := 300)
  sorry
