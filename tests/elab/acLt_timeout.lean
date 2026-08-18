axiom sumRange (n : Nat) (f : Nat → Nat) : Nat
axiom sumRange_add (m n) (f : Nat → Nat) :
  sumRange (m + n) f = sumRange m f + sumRange n (f <| m + ·)

/--
error: Tactic `simp` failed with a nested error:
(deterministic) timeout at `«Lean.Meta.acLt»`, maximum number of heartbeats (200000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
example (k : Nat) (a : Fin (1 + k + 1) → Nat) :
    0 ≤ sumRange (1 + k + 1) (fun i =>
        if h : i < 1 + k + 1 then a ⟨i, h⟩ else 0) := by
  simp only [Nat.add_comm, sumRange_add]
