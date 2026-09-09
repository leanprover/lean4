module

/-! Test that recursion depth exhaustion in `omega`'s preliminary assumption check
does not prevent the arithmetic solver from running. -/

example (m : Nat) (_h : m * 1000 ≤ 0) :
    (1000 : Nat) * 1000 ≤ 1000 * 1000 := by
  omega

example (m k : Nat) (_h : m * 1000 ≤ 0) : k * 1000 ≤ k * 1000 := by
  omega

example (m : Nat) (_h : m * 2 ^ 64 ≤ (2 ^ 64 - 1) * 2 ^ 64) :
    (2 ^ 64 - 1) * (2 ^ 64 * 2 ^ 64) + (2 ^ 64 - 1) * 2 ^ 64 + 2 ^ 64 ≤
      2 ^ 64 * (2 ^ 64 * 2 ^ 64) := by
  omega

class Value where
  val : Nat

instance : Value := ⟨1000⟩

-- The assumption check must still unfold instances for non-arithmetic goals.
example (P : Nat → Prop) (_h : P Value.val) : P 1000 := by
  omega
