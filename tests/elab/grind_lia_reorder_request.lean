/-!
Dynamic variable reordering in the `lia` model search. When a Cooper split with many cases is about
to open and no Cooper case is open yet, the split variable is ordered first and the search restarts,
so that the conflict surfaces at a variable with a smaller coefficient. Each goal below needed a
`2^32`-way or `65536`-way split with the static order.
-/
set_option linter.unusedVariables false
-- three-limb counter increment, top limb
example (x4 x5 x6 x7 : Int)
    (h4 : 0 ≤ x4 ∧ x4 ≤ 2 ^ 32 - 1) (h5 : 0 ≤ x5 ∧ x5 ≤ 2 ^ 32 - 1)
    (h6 : 0 ≤ x6 ∧ x6 ≤ 2 ^ 32 - 1) (h7 : 0 ≤ x7 ∧ x7 ≤ 2 ^ 32 - 1) :
    (x7 + if (x6 + if (x5 + x4) % 4294967296 < x4 then 1 else 0) % 4294967296 < x6 then 1 else 0) % 4294967296
      = (x5 + (4294967296 * x6 + (18446744073709551616 * x7 + x4))) % 79228162514264337593543950336 / 18446744073709551616 := by lia

-- two-limb counter increment over `Nat`
example (x4 x5 x6 : Nat) (h4 : x4 < 2 ^ 32) (h5 : x5 < 2 ^ 32) (h6 : x6 < 2 ^ 32) :
    (x6 + if (x5 + x4) % 4294967296 < x4 then 1 else 0) % 4294967296 = (x5 + (4294967296 * x6 + x4)) % 18446744073709551616 / 4294967296 := by lia

example (x0 x1 x2 : Nat) (h0 : x0 < 12) (h1 : x1 < 65536) : (x0 + 5 * x2) % 67108864 / 65536 = (x0 + 5 * x2) / 65536 % 1024 := by lia

-- nested splits of 880 cases
example (x0 x1 x2 : Int) (h0 : 0 ≤ x0 ∧ x0 < 64) (h1 : -60 ≤ x1 ∧ x1 < 1024) (h2 : (x1 + -2 * x0 + -62) ≤ ((((x1 / 5) / 256) * 256) / 4294967296)) (h3 : x0 = ((x2 / 12) / 1024)) (h4 : ((((10 * x2 + 5 * x1 + -73) / 8) % 60) % 5) = -64 * x0 + 2 * x1 + -7 * x2 + -99) : (if (x1 + 1000 * x0 + -1 * x2 + 100) = -100 * x0 + 10 * x1 + -12 then 3 else 0) + -2 * x1 + 2 * x2 ≤ (x0 % 64) := by lia
