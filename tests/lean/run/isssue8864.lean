axiom testSorry : α
opaque a : Nat
opaque b : Nat
opaque f : Nat → Nat
opaque P : Nat → Prop
theorem ab : a = b := testSorry
theorem ba : b = a := testSorry
theorem fafb : f a = f b := testSorry

/--
error: unsolved goals
⊢ P (f b)
-/
#guard_msgs in example : P (f a) := by simp [fafb, ba]

/--
error: tactic 'simp' failed, nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : P (f a) := by simp [ab, ba]
