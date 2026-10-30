/-!
Variable ordering in the `lia` solver: variables with equal coefficient costs are ordered so that a
variable occurring only with large coefficients (e.g., `t / 64`, which occurs only as `64 * (t / 64)`)
is assigned before variables with unit occurrences. Otherwise, `t / 64` became the conflicting
variable and `lia` exceeded `liaSteps` in two nested 64-way (resp. `2^32`-way) Cooper splits.
These goals were reported as examples where `omega` succeeds and `lia` fails.
-/

example (y t : Int) (h0 : 0 ≤ y) (h1 : y < 64) : t % 64 ≤ (64 * t + y) % 4096 / 64 := by lia

-- 32-bit counter increment with carry into the high word
example (n0 : Nat) (x1 : Int) (x2 : Int) (x3 : Int) (x4 : Int) (x5 : Int) (x6 : Int) (h0 : n0 = 2) (h1 : 0 ≤ x1 ∧ x1 ≤ 2 ^ 8 - 1) (h2 : 0 ≤ x2 ∧ x2 ≤ 2 ^ 64 - 1) (h3 : 0 ≤ x3 ∧ x3 ≤ 2 ^ 64 - 1) (h4 : 0 ≤ x4 ∧ x4 ≤ 2 ^ 32 - 1) (h5 : 0 ≤ x5 ∧ x5 ≤ 2 ^ 32 - 1) (h6 : 0 ≤ (x5 + x4) % 4294967296 ∧ (x5 + x4) % 4294967296 ≤ 2 ^ 32 - 1) (h7 : 0 ≤ x6 ∧ x6 ≤ 2 ^ 32 - 1) (h8 : 0 ≤ (x6 + if (x5 + x4) % 4294967296 < x4 then 1 else 0) % 4294967296 ∧ (x6 + if (x5 + x4) % 4294967296 < x4 then 1 else 0) % 4294967296 ≤ 2 ^ 32 - 1) : (x6 + if (x5 + x4) % 4294967296 < x4 then 1 else 0) % 4294967296 = (x5 + (4294967296 * x6 + x4)) % 18446744073709551616 / 4294967296 := by lia

-- As originally captured
example (n0 : Nat) (x1 : Int) (x2 : Int) (x3 : Int) (x4 : Int) (x5 : Int) (x6 : Int) (h0 : n0 = 2) (h1 : 0 ≤ x1 ∧ x1 ≤ 2 ^ 8 - 1) (h2 : 0 ≤ x2 ∧ x2 ≤ 2 ^ 64 - 1) (h3 : 0 ≤ x3 ∧ x3 ≤ 2 ^ 64 - 1) (h4 : 0 ≤ x4 ∧ x4 ≤ 2 ^ 32 - 1) (h5 : 0 ≤ x5 ∧ x5 ≤ 2 ^ 32 - 1) (h6 : 0 ≤ (x5 + x4) % 4294967296 ∧ (x5 + x4) % 4294967296 ≤ 2 ^ 32 - 1) (h7 : 0 ≤ x6 ∧ x6 ≤ 2 ^ 32 - 1) (h8 : 0 ≤ (x6 + if (x5 + x4) % 4294967296 < x4 then 1 else 0) % 4294967296 ∧ (x6 + if (x5 + x4) % 4294967296 < x4 then 1 else 0) % 4294967296 ≤ 2 ^ 32 - 1) : (x6 + if (x5 + x4) % 4294967296 < x4 then 1 else 0) % 4294967296 = (x5 + (4294967296 * x6 + x4)) % 18446744073709551616 / 4294967296 := by lia
