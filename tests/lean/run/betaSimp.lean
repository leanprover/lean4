opaque f : Nat → Nat
@[simp] axiom f_ax : f (no_index 0) = 1
example : f ((fun x => x) 0) = 1 := by
  fail_if_success simp -beta -- should fail
  simp
