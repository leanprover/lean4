/-!
Divisibility constraints with large moduli in `lia`. The solver normalizes `d ∣ p` by reducing the
coefficients of `p` modulo `d` and making the leading coefficient `±1` (e.g., `32768 ∣ 5*x` becomes
`32768 ∣ x`), and tightens bounds whose value is known modulo a divisor of `d`. Previously, each of
these goals produced a Cooper split with as many cases as the modulus.
-/

example (x : Int) (h : 65536 ∣ 10 * x) : 32768 ∣ x := by lia
example (x : Int) (h1 : 1024 ∣ x) (h2 : 1000 ∣ x) : 128000 ∣ x := by lia
example (x y : Int) (h : 65536 ∣ 10 * x + y) : 4 ∣ 10 * x - y := by lia
example (x y : Int) (h : 65536 ∣ 1000 * x + 100 * y) : 4 ∣ 10 * x - y := by lia
example (x : Int) (h1 : 3 ∣ x - 2) (h2 : 5 ∣ x - 3) : 15 ∣ x - 8 := by lia
example (x0 x1 : Int) (h0 : (((x0 / 16) % 100) % 4096) = -10 * x0 + 23) (h1 : 16 ∣ 2 * x1 + 2 * x0 + 42) (h2 : 65536 ∣ 10 * x0 + -88) : 12 ∣ 7 * x0 + -5 * x1 := by lia
example (x0 x1 x2 x3 : Int) (h0 : 0 ≤ x1) (h1 : 0 ≤ x2) (h2 : -16 ≤ x3) (h3 : (((64 * x0 + -1 * x2 + x1) / 1024) / 100) = -2 * x0) (h4 : 65536 ∣ 1000 * x0 + 100 * x3) : 4 ∣ 10 * x0 + -1 * x3 + 100 * x2 := by lia
example (x : Nat) (h : 65536 ∣ 10 * x) : 32768 ∣ x := by lia
example (x : Nat) (h1 : 1024 ∣ x) (h2 : 1000 ∣ x) : 128000 ∣ x := by lia

/-!
Goals whose Cooper splits were avoided by the tightening. The first two took 44s and 25s before,
with most of the time spent in kernel type checking of the enumerated cases.
-/
example (y t : Nat) (h1 : y < 64) : t % 64 ≤ (64 * t + y) % 4096 / 64 := by lia
example (x : Nat) : x % 65536 / 256 = x / 256 % 256 := by lia
example (y z w t : Int) (h0 : 0 ≤ y) (h1 : y < 64)
    (h2 : 0 ≤ 128 * t + z) (h3 : 128 * t + z ≤ 8191)
    (h4 : 0 ≤ 128 * ((64 * t + y) % 4096 / 64) + w) (h5 : 128 * ((64 * t + y) % 4096 / 64) + w ≤ 8191) :
    t % 64 ≤ (64 * t + y) % 4096 / 64 := by lia
