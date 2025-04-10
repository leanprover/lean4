example (f : (Nat → Nat) → Nat) : a = b → f (fun x => a + x) = f (fun x => b + x) := by
  grind

example (f : (Nat → Nat) → Nat) : a = b → f (fun x => a + x) = f (fun x => b + x) := by
  fail_if_success grind -funext
  sorry
