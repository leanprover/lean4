module

/-!
Regression test: `Array.instDecidableEqImpl` is `@[expose]`, so `decide`/`rfl`
over `Array` equality reduces in the kernel under the module system, including
when both arrays are nonempty. Previously reduction got stuck at
`instDecidableEqImpl`, whose body was not exposed downstream.
-/

example : (#[0, 1] : Array Nat) ≠ #[1] := by decide
example : (#[2, 3] : Array Nat) = #[2, 3] := by decide
example : ¬ ((#[0, 1] : Array Nat) = #[1, 0]) := by decide
example : decide ((#[0, 1] : Array Nat) = #[0, 1]) = true := by rfl
