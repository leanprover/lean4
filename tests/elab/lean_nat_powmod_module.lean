module
import Init

/-! Definitional reduction of `Nat.powMod` from a module importer.
These tests exercise exposure and ordinary Meta reduction in all three size ranges. -/

example : Nat.powMod 3 4 5 = 1 := rfl
example : Nat.powMod 3 3 (Nat.shiftLeft 1 600) = 27 := by decide
example : Nat.powMod 3 3 (Nat.shiftLeft 1 1100) = 27 := by decide
example (b m : Nat) : Nat.powMod b 0 m = 1 % m := rfl
