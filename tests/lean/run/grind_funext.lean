
set_option grind.warning false

example (f : (Nat → Nat) → Nat → Nat → Nat) : a = b → f (fun x => a + x) 1 b = f (fun x => b + x) 1 a := by
  grind

example (f : (Nat → Nat) → Nat) : a = b → f (fun x => a + x) = f (fun x => b + x) := by
  fail_if_success grind -funext
  sorry

example (g : Nat → Nat → Nat) (f : (Nat → Nat) → Nat → (Nat → Nat) → Nat) :
    a = b → f (fun x => a + x) 1 (fun x => g x a) = f (fun x => x + b) 1 (fun x => g x b) := by
  grind
