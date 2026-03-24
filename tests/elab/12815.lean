/-! Diagnostics from induction alternatives must not be swallowed when the `using`
clause contains a nested `by` tactic block. https://github.com/leanprover/lean4/issues/12815 -/

axiom myElim (h : True) (P : Nat → Prop) (n : Nat)
    (zero : P 0) (succ : ∀ n, P n → P (n + 1)) : P n

/--
error: unsolved goals
case zero
⊢ True
-/
#guard_msgs in
theorem foo : True := by
  induction 0 using myElim (by trivial) with
  | zero => skip
  | succ _ ih => exact ih
