/-!
It used to be that aux theorems could only be created within declarations. But with `omega` wanting
to create an aux theorem, and `omega` being used in, say, `variable` commands, this is not tenable.
-/

structure Foo (n : Nat) (h : n > 1 := by omega) : Type

set_option pp.proofs true

/-- info: Foo 3 (Decidable.byContradiction fun a => _check._proof_1 a) : Type -/
#guard_msgs in
#check Foo 3

variable (x : Foo 2)

/-- info: x : Foo 2 (Decidable.byContradiction fun a => _proof_1 a) -/
#guard_msgs in
#check x
