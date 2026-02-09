module
example (f : (Nat → Nat) → Nat → Nat → Nat) : a = b → f (fun x => a + x) 1 b = f (fun x => b + x) 1 a := by
  grind

example (f : (Nat → Nat) → Nat) : a = b → f (fun x => a + x) = f (fun x => b + x) := by
  -- This test used to check `fail_if_success grind -funext`,
  -- but now it succeeds even without funext
  -- due to adding the eta rule in https://github.com/leanprover/lean4/pull/7977.
  grind

example (g : Nat → Nat → Nat) (f : (Nat → Nat) → Nat → (Nat → Nat) → Nat) :
    a = b → f (fun x => a + x) 1 (fun x => g x a) = f (fun x => x + b) 1 (fun x => g x b) := by
  grind
