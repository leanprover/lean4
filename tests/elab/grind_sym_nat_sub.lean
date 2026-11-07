/-!
Tests for the cancellation of the common part of the sides of a `Nat` subtraction in the
`Sym.simp`-based `grind` normalizer (`Sym.Simp.simpNatSub`). Numeral offsets are cancelled as by
the legacy `Nat.reduceSubDiff` simproc, and so are common monomials.
-/

set_option warn.sorry false

-- Numeral offsets: both normalizers agree.
#guard_msgs in
example (n : Nat) (f : Nat → Nat) : f (n + 1 - 1) = 0 := by grind_norm check; sorry

#guard_msgs in
example (n : Nat) (f : Nat → Nat) : f (n + 2 - 1) = 0 := by grind_norm check; sorry

#guard_msgs in
example (n : Nat) (f : Nat → Nat) : f (n + 1 - 3) = 0 := by grind_norm check; sorry

#guard_msgs in
example (n : Nat) (f : Nat → Nat) : f (3 - (n + 1)) = 0 := by grind_norm check; sorry

#guard_msgs in
example (n : Nat) (f : Nat → Nat) : f (1 - (n + 1)) = 0 := by grind_norm check; sorry

#guard_msgs in
example (n m : Nat) (f : Nat → Nat) : f (n + 3 - (m + 1)) = 0 := by grind_norm check; sorry

/--
trace: n : Nat
f : Nat → Nat
⊢ f n = 0
-/
#guard_msgs in
example (n : Nat) (f : Nat → Nat) : f (n + 1 - 1) = 0 := by grind_norm sym; trace_state; sorry

-- Common monomials.
/--
trace: n k : Nat
f : Nat → Nat
⊢ f n = 0
-/
#guard_msgs in
example (n k : Nat) (f : Nat → Nat) : f (n + k - k) = 0 := by grind_norm sym; trace_state; sorry

/--
trace: x y z : Nat
f : Nat → Nat
⊢ f (2 - z) = 0
-/
#guard_msgs in
example (x y z : Nat) (f : Nat → Nat) : f (x * y + 3 - (x * y + z + 1)) = 0 := by
  grind_norm sym; trace_state; sorry

/--
trace: x y : Nat
f : Nat → Nat
⊢ f (x + y) = 0
-/
#guard_msgs in
example (x y : Nat) (f : Nat → Nat) : f (3 * x + y - 2 * x) = 0 := by
  grind_norm sym; trace_state; sorry

/--
trace: x y : Nat
f : Nat → Nat
⊢ f (x - y) = 0
-/
#guard_msgs in
example (x y : Nat) (f : Nat → Nat) : f (2 * x + 1 - (x + y + 1)) = 0 := by
  grind_norm sym; trace_state; sorry

-- The minuend is entirely cancelled.
/--
trace: x y : Nat
f : Nat → Nat
⊢ f 0 = 0
-/
#guard_msgs in
example (x y : Nat) (f : Nat → Nat) : f (x + 1 - (2 * x + y + 1)) = 0 := by
  grind_norm sym; trace_state; sorry

-- A kept product (`distrib := false`) is a monomial of its own.
/--
trace: x y : Nat
f : Nat → Nat
⊢ f 2 = 0
-/
#guard_msgs in
example (x y : Nat) (f : Nat → Nat) : f (x * (y + 1) + 2 - x * (y + 1)) = 0 := by
  grind_norm sym; trace_state; sorry

-- The result takes part in the enclosing polynomial.
/--
trace: n : Nat
f : Nat → Nat
⊢ f (2 * n + 1) = 0
-/
#guard_msgs in
example (n : Nat) (f : Nat → Nat) : f (2 * (n + 1 - 1) + 1) = 0 := by
  grind_norm sym; trace_state; sorry

/--
trace: n m : Nat
⊢ m ≤ n
-/
#guard_msgs in
example (n m : Nat) : m ≤ n + 2 - 2 := by grind_norm sym; trace_state; sorry

-- Nothing in common: left alone.
/--
trace: x y : Nat
f : Nat → Nat
⊢ f (x - y) = 0 ∧ f (2 * x - 3 * y) = 0 ∧ f (x - (y + 1)) = 0
-/
#guard_msgs in
example (x y : Nat) (f : Nat → Nat) : f (x - y) = 0 ∧ f (2 * x - 3 * y) = 0 ∧ f (x - (y + 1)) = 0 := by
  grind_norm sym; trace_state; sorry

-- Under a binder.
/--
trace: f : Nat → Nat
⊢ ∀ (x : Nat), f x = 0
-/
#guard_msgs in
example (f : Nat → Nat) : ∀ x, f (x + 1 - 1) = 0 := by grind_norm sym; trace_state; sorry

set_option backward.grind.normalizer false

-- `[:n].size` unfolds to `n + 1 - 1`. Cutsat knows that it is `n`, but under an uninterpreted
-- `Prop` context only congruence closes the goal, so the normal form must be `n`.
example (n m : Nat) (p : Prop → Prop) (h : p (m ≤ n + 1 - 1)) : p (m ≤ n) := by grind

example (n m : Nat) (p : Prop → Prop) (h : p (m ≤ [:n].size)) : p (m ≤ n) := by grind

example (n m k : Nat) (p : Prop → Prop) (h : p (m ≤ n + k - k)) : p (m ≤ n) := by grind
