/-!
The rational model search of the `lia` solver used to loop until `liaSteps` on these goals: a variable
is assigned a non-integer value, so the tail of a divisibility constraint on a later variable evaluates
to a non-integer. That case must be skipped (the model is already imprecise and the integer search takes
over), but it was reported like "no solutions", and the resolvent of that spurious conflict did not change
anything, two steps per cycle. The same happened when the conflict was real but the resolvent landed on a
variable whose rational value already ignores its constraints. All goals are provable by `omega`.
-/
set_option linter.unusedVariables false

example (x0 x1 x2 x3 : Int) (h0 : 0 ≤ x0 ∧ x0 < 65536) (h1 : -7 ≤ x1) (h2 : 5 * (3 * x0 + x2) ≤ 5 * x0 + 64 * x2 + 33 ∧ 5 * x0 + 64 * x2 + 33 < 5 * (3 * x0 + x2) + 5) (h3 : 100 * (5 * x0 + 64 * x2 + 33) ≤ 10 * x1 + -64 * x3 + 1000 * x0 ∧ 10 * x1 + -64 * x3 + 1000 * x0 < 100 * (5 * x0 + 64 * x2 + 33) + 100) (h4 : 3 * (10 * x1 + -64 * x3 + 1000 * x0) ≤ 10 * x3 + -35 ∧ 10 * x3 + -35 < 3 * (10 * x1 + -64 * x3 + 1000 * x0) + 3) (h5 : 5 * (10 * x3 + -35) ≤ 2 * x1 + 3 * x0 ∧ 2 * x1 + 3 * x0 < 5 * (10 * x3 + -35) + 5) : ((((((x0 + -2 * x1 + -22) / 100) * 100) / 1000) / 65536) * 65536) < 5 * x1 + x0 + -1 * x3 + -47 := by lia

example (x0 x1 x2 : Int) (h0 : -65536 ≤ x1) (h1 : 0 ≤ x2) (h2 : 5 * (3 * x0 + 100 * x1 + -28) ≤ 1000 * x0 + 73 ∧ 1000 * x0 + 73 < 5 * (3 * x0 + 100 * x1 + -28) + 5) (h3 : 7 * (1000 * x0 + 73) ≤ x2 + 7 * x1 + 11 ∧ x2 + 7 * x1 + 11 < 7 * (1000 * x0 + 73) + 7) : ((((x1 % 60) / 10) * 10) / 1000) ≤ (((5 * x1 + -42) / 60) / 7) := by lia

example (x0 x1 : Int) (h0 : 3 * (10 * x1 + -2 * x0 + 52) ≤ 2 * x0 + -65 ∧ 2 * x0 + -65 < 3 * (10 * x1 + -2 * x0 + 52) + 3) (h1 : 64 * (2 * x0 + -65) ≤ 2 * x0 + 3 * x1 + -65 ∧ 2 * x0 + 3 * x1 + -65 < 64 * (2 * x0 + -65) + 64) : ((x1 % 4096) % 256) = 7 * x1 + 10 * x0 + -75 := by lia

example (x0 : Int) (q0 r0 q1 r1 : Int) (h0 : 0 ≤ x0 ∧ x0 < 4096) (h1 : q0 = (-3 * x0) / 60) (h2 : r0 = (-3 * x0) % 60) (h3 : q1 = (-1 * r0 + -2 * x0 + -90) / 1000) (h4 : r1 = (-1 * r0 + -2 * x0 + -90) % 1000) (h5 : (((1000 * q1) / 2) / 100) = 2 * x0 + 10 * q0 + 100 * q1 + -95) (h6 : ((q0 / 12) * 12) = (((x0 / 1024) / 4294967296) / 3)) : (((((2 * x0 + 58) / 4096) * 4096) / 100) % 3) = -5 * q1 + q0 + 70 := by lia
