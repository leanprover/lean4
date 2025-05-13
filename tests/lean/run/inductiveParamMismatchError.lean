/-! # Inductive parameter mismatch error messages

Tests that appropriate error messages are shown when the fixed parameters of an inductive type
constructor are omitted or incorrect in an `inductive` declaration.

A previous version of one such error message was noted to be confusing in #2195:
https://github.com/leanprover/lean4/issues/2195
-/

inductive Forall {α : Type u} (p : α → Prop) : List α → Prop
  | nil  : Forall p ([] : List α)
  | cons : ∀ {x xs}, p x → Forall p xs → Forall p (x :: xs)

/--
error: Missing parameters in occurrence of inductive type: In the expression
  Forall IsSmart params
found
  IsSmart
but expected all parameters to be specified:
  IsSmart d

Note: All occurrences of an inductive type in the types of its constructors must include its fixed parameters. To allow partial application of the type constructor without specifying this parameter, make it an index instead.
-/
#guard_msgs in
inductive IsSmart (d : Nat) : Prop
  | isSmart: ∀
    (name : String)
    (hash : UInt64)
    (reader : Bool),
    Forall IsSmart params
    → IsSmart d

abbrev NatOf (F : Type → Type) : Type := F Nat

/--
error: Missing parameters in occurrence of inductive type: In the expression
  NatOf T
found
  T
but expected all parameters to be specified:
  T α

Note: All occurrences of an inductive type in the types of its constructors must include its fixed parameters. To allow partial application of the type constructor without specifying this parameter, make it an index instead.
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

abbrev InList : List (Type → Type) → Type :=
  fun _ => Nat

/--
error: Missing parameters in occurrence of inductive type: In the expression
  [Foo]
found
  Foo
but expected all parameters to be specified:
  Foo α

Note: All occurrences of an inductive type in the types of its constructors must include its fixed parameters. To allow partial application of the type constructor without specifying this parameter, make it an index instead.
-/
#guard_msgs in
inductive Foo (α : Type) : Type
  | mk : InList [Foo] → Foo α

/--
error: Missing parameters in occurrence of inductive type: In the expression
  NatOf (Bar α)
found
  Bar α
but expected all parameters to be specified:
  Bar α β

Note: All occurrences of an inductive type in the types of its constructors must include its fixed parameters. To allow partial application of the type constructor without specifying this parameter, make it an index instead.
-/
#guard_msgs in
inductive Bar (α β : Type) : Type
  | mk : NatOf (Bar α) → Bar α β
