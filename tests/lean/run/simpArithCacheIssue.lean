/--
info: x y : Nat
h : y = 0
⊢ id (2 * x + y) = id (2 * x)
-/
#guard_msgs in
example (x y : Nat) (h : y = 0) : id ((x + x) + y) = id (x + x) := by
  simp +arith only
  /-
  This is a test for a `simp` cache issue where the following incorrect goal was being
  produced.
  ```
  ... |- id (2*x + y) = id (x + x)
  ```
  instead of
  ```
  ... |- id (2*x + y) = id (2*x)
  ```
  -/
  trace_state
  simp [h]

example (x y : Nat) (h : y = 0) : id (x + x) = id ((x + x) + y) := by
  simp +arith only
  simp [h]
