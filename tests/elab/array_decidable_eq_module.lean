module

/-!
Tests kernel reduction of `Array` equality across a module boundary.
-/

example : (#[0, 1] : Array Nat) ≠ #[1] := by decide
example : (#[2, 3] : Array Nat) = #[2, 3] := by decide
example : ¬ ((#[0, 1] : Array Nat) = #[1, 0]) := by decide
example : decide ((#[0, 1] : Array Nat) = #[0, 1]) = true := by rfl
example : (#[1, 2, 3] : Array Nat) ≠ #[1, 2, 4] := by decide +kernel

-- Empty cases already reduced before the nonempty implementation was exposed.
example : (#[] : Array Nat) = #[] := by decide
example : (#[] : Array Nat) ≠ #[1] := by decide
