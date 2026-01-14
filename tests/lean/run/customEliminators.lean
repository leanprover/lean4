/-!
# Tests for the custom eliminators feature for `induction` and `cases`
-/

/-!
Test the built-in custom `Nat` eliminator.
-/
/--
error: unsolved goals
case zero
P : Nat → Prop
⊢ P 0

case succ
P : Nat → Prop
n✝ : Nat
a✝ : P n✝
⊢ P (n✝ + 1)
-/
#guard_msgs in
example (P : Nat → Prop) : P n := by
  induction n
  done

/-!
Turn off the built-in custom `Nat` eliminator.
-/
section
set_option tactic.customEliminators false

/--
error: unsolved goals
case zero
P : Nat → Prop
⊢ P Nat.zero

case succ
P : Nat → Prop
n✝ : Nat
n_ih✝ : P n✝
⊢ P n✝.succ
-/
#guard_msgs in
example (P : Nat → Prop) : P n := by
  induction n
  done

end
