opaque A : Nat → Type
opaque f (x : Nat) (a : A x) : Nat

example (x : Nat) (a : A (x + 0)) : f (x + 0) a = x := by
  simp
  trace_state -- ⊢ f x a = x
  sorry

example (x : Nat) (a : A (x + 0)) : f (x + 0) a = x := by
  simp (config := { dsimp := false, failIfUnchanged := false })
  trace_state -- ⊢ f (x + 0) a = x
  sorry
