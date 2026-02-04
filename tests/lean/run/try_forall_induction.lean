/-!
# Tests for `try?` with forall-quantified goals

When the goal has leading foralls, `try?` should still find induction-based proofs
by collecting candidates from under the forall binders.

These examples require function induction to solve. With n in context, try?
finds `fun_induction fib/double`. With ∀ n, try? should also find the proof
(by doing intro first, then function induction).
-/

-- A recursive function where proofs require function induction
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

-- Another simple recursive function
def double : Nat → Nat
  | 0 => 0
  | n + 1 => double n + 2

/-! ## Baseline tests: n in context (these already work) -/

example (n : Nat) : n ≤ fib n + 1 := by try?
example (n : Nat) : double n = 2 * n := by try?

/-! ## Forall tests: these should also work (after intro + function induction) -/

example : ∀ n, n ≤ fib n + 1 := by try?
example : ∀ n, double n = 2 * n := by try?

/-! ## Multiple function induction candidates under forall -/

-- When there are multiple calls to the same function, fun_induction needs to specify which call
example : ∀ n m, fib n + fib m = fib m + fib n := by try?

/-! ## Regular induction under forall (not just function induction) -/

inductive MyNat where | zero | succ : MyNat → MyNat

example : ∀ n : MyNat, n = MyNat.zero ∨ ∃ m, n = MyNat.succ m := by try?
