/-! # Inductive parameter mismatch error messages

Tests that appropriate error messages are shown when the fixed parameters of an inductive type
constructor are omitted or incorrect in an `inductive` declaration.
-/

abbrev NatOf (F : Type → Type) : Type := F Nat

/--
error: Missing parameters in occurrence of inductive type: Found
  T
but expected
  T α

Note: All occurrences of an inductive type in the types of its constructors must include its fixed parameters. To omit a parameter, make it an index instead.
-/
#guard_msgs in
inductive T (α : Type) where
  | mk : NatOf T → T α

inductive T_OK (α : Type) : Type → Type where
  | mk : NatOf (T_OK α) → T_OK α Nat

/--
error: Mismatched inductive type parameters in
  BadIdx α 0
The provided argument
  0
is not definitionally equal to the expected parameter
  n

Note: The value of parameter 'n' must be fixed throughout the inductive declaration. Consider making this parameter an index if it must vary between occurrences in constructor types.
-/
#guard_msgs in
inductive BadIdx (α : Type) (n : Nat) : Type 1
  | mk : BadIdx α 0
