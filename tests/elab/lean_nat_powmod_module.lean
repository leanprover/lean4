module
import Init

/-! Definitional reduction of `Nat.powMod` from a module importer.
These tests exercise exposure and ordinary Meta reduction in the size ranges and base-dependent paths. -/

example : Nat.powMod 3 4 5 = 1 := rfl
example : Nat.powMod 3 3 (Nat.shiftLeft 1 600) = 27 := by decide
example : Nat.powMod 3 3 (Nat.shiftLeft 1 1100) = 27 := by decide
example (b m : Nat) : Nat.powMod b 0 m = 1 % m := rfl

/-! Small-base dispatch boundaries, including bases requiring reduction first.
The direct powers have exponent at most 101, so the independent arithmetic
reference remains small enough for kernel evaluation. -/
example : [1024, 4096].all (fun bits =>
    [Nat.shiftLeft 1 bits - 1, Nat.shiftLeft 1 bits, Nat.shiftLeft 1 bits + 1].all (fun m =>
      [17, Nat.shiftLeft 1 64 - 1, Nat.shiftLeft 1 64, m + 17].all (fun b =>
        [0, 1, 3, 4, 5, 101].all (fun e =>
          Nat.powMod b e m == (b % m) ^ e % m)))) := by decide +kernel
example : Nat.powMod 17 101 (Nat.shiftLeft 1 5000) = 17 ^ 101 := by decide
-- Full-size exponents exercise the large-modulus kernel recursion depth.
set_option maxRecDepth 65536 in
example : Nat.powMod 2 (Nat.shiftLeft 1 5000) (Nat.shiftLeft 1 4096 + 1) = 1 := by
  decide +kernel
