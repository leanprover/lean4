/-!
Equations without a unit coefficient are eliminated in `lia` as in the Omega test: for the smallest
coefficient `k`, the equation is reduced modulo `m := |k| + 1`, the witness `σ := p̄ / m` is a new
variable with `p̄ = m*σ`, which has a unit coefficient and is eliminated exactly, and the process
repeats on the original equation with shrinking coefficients. Previously such an equation was
eliminated by a solved form scaled by `k`, which multiplied all other constraints by `k`; chains of
these produced bounds with coefficients in the thousands and Cooper splits with as many cases.
-/
set_option linter.unusedVariables false
example (x y : Int) (h : 3 * x + 5 * y = 1) : x % 5 = 2 := by lia
example (x y : Int) (h : 3 * x + 5 * y = 1) : y % 3 = 2 := by lia
example (x y : Int) (h : 1000 * x - 999 * y = 1) : x % 999 = 1 := by lia
example (x y : Int) (h : 6 * x + 10 * y = 3) : False := by lia
example (x y : Int) (h : 7 * x + 11 * y = 100) (hx : 0 ≤ x) (hy : 0 ≤ y) : x = 8 ∧ y = 4 := by lia

-- found by random generation; `omega` proves it in 0.3s, `lia` enumerated 1525-case splits
example (x0 q0 r0 q1 r1 : Int) (h0 : 0 ≤ x0) (h1 : q0 = (100 * x0 + 56) / 4096) (h2 : r0 = (100 * x0 + 56) % 4096) (h3 : q1 = (3 * r0) / 10) (h4 : r1 = (3 * r0) % 10) (h5 : (3 * q0 + 7 * q1 + r0 + -94) = 5 * x0 + -28) : ((q1 % 4096) % 8) < 10 * q0 := by lia
