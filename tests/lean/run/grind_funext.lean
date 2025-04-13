
set_option grind.warning false

example (f : (Nat → Nat) → Nat → Nat → Nat) : a = b → f (fun x => a + x) 1 b = f (fun x => b + x) 1 a := by
  grind

example (f : (Nat → Nat) → Nat → Nat → Nat) : a = b → f (fun x => a + x) 1 b = f (fun x => b + x) 1 a := by
  grind (splits := 0)

example (f : (Nat → Nat) → Nat → Nat → Nat) : a = b → f (fun x => a + x) 1 b = f (fun x => b + x) 1 a := by
  grind -lookahead

example (f : (Nat → Nat) → Nat → Nat → Nat) : a = b → f (fun x => a + x) 1 b = f (fun x => b + x) 1 a := by
  fail_if_success grind -lookahead (splits := 0) -- We need lookahead of case-splits
  sorry

example (f : (Nat → Nat) → Nat) : a = b → f (fun x => a + x) = f (fun x => b + x) := by
  fail_if_success grind -funext
  sorry

-- Lookahead is not tried because it will not make the applications congruent
/-- info: [grind.lookahead.add] (fun x => b + x) = fun x => a + x -/
#guard_msgs (info) in
set_option trace.grind.lookahead true in
example (f : (Nat → Nat) → Nat → Nat → Nat) : a = b → f (fun x => a + x) 1 b = f (fun x => b + x) 1 2 := by
  fail_if_success grind
  sorry

example (g : Nat → Nat → Nat) (f : (Nat → Nat) → Nat → (Nat → Nat) → Nat) :
    a = b → f (fun x => a + x) 1 (fun x => g x a) = f (fun x => x + b) 1 (fun x => g x b) := by
  grind
