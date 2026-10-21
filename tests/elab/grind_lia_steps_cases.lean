/-!
`liaSteps` also bounds the cases of Cooper and disequality splits in `lia`. The next case of a split
can be refuted as soon as it is asserted, so an enumeration of thousands of cases never reached the
step check in the main loop. On this goal, the solver used to enumerate 1525-case splits to the end
and produce a proof the kernel rejects with "deep recursion detected".
-/

example (x0 q0 r0 q1 r1 : Int) (h0 : 0 ≤ x0) (h1 : q0 = (100 * x0 + 56) / 4096) (h2 : r0 = (100 * x0 + 56) % 4096) (h3 : q1 = (3 * r0) / 10) (h4 : r1 = (3 * r0) % 10) (h5 : (3 * q0 + 7 * q1 + r0 + -94) = 5 * x0 + -28) : ((q1 % 4096) % 8) < 10 * q0 := by
  fail_if_success lia (liaSteps := 300)
  sorry
