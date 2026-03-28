/-! # Inductive parameter mismatch error messages

Tests that appropriate error messages are shown when the fixed parameters of an inductive type
constructor are omitted or incorrect in an `inductive` declaration.

A previous version of one such error message was noted to be confusing in #2195:
https://github.com/leanprover/lean4/issues/2195
-/

/-! ## Example from Issue #2195 -/

inductive Desc where
  | intro
    (name: String)
    (hash: UInt64)
    (params: List Desc)
  : Desc
  deriving Repr

def hash_with_name (_name: String) (_params: List Desc): UInt64 := 0 -- mock hash function

def Desc.intro_func (name: String) (params: List Desc): Desc :=
  Desc.intro
    name
    (hash_with_name name params)
    params

inductive Forall {α : Type u} (p : α → Prop) : List α → Prop
  | nil  : Forall p ([] : List α)
  | cons : ∀ {x xs}, p x → Forall p xs → Forall p (x :: xs)

/--
error: Missing parameter(s) in occurrence of inductive type: In the expression
  Forall IsSmart params
found
  IsSmart
but expected all parameters to be specified:
  IsSmart d

Note: All occurrences of an inductive type in the types of its constructors must specify its fixed parameters. Only indices can be omitted in a partial application of the type constructor.
-/
#guard_msgs in
inductive IsSmart (d: Desc): Prop
  | isSmart: ∀
    (name: String)
    (params: List Desc)
    (hash: UInt64)
    (reader: Bool),
    d = Desc.intro name hash params
    → hash = hash_with_name name params
    → Forall IsSmart params
    → IsSmart d


/-! ## "Missing parameter" error -/

abbrev NatOf (F : Type → Type) : Type := F Nat
/--
error: Missing parameter(s) in occurrence of inductive type: In the expression
  NatOf T
found
  T
but expected all parameters to be specified:
  T α

Note: All occurrences of an inductive type in the types of its constructors must specify its fixed parameters. Only indices can be omitted in a partial application of the type constructor.
-/
#guard_msgs in
inductive T (α : Type) where
  | mk : NatOf T → T α

inductive T_OK (α : Type) : Type → Type where
  | mk : NatOf (T_OK α) → T_OK α Nat

/--
error: Missing parameter(s) in occurrence of inductive type: In the expression
  NatOf (T₂ α)
found
  T₂ α
but expected all parameters to be specified:
  T₂ α β

Note: All occurrences of an inductive type in the types of its constructors must specify its fixed parameters. Only indices can be omitted in a partial application of the type constructor.
-/
#guard_msgs in
inductive T₂ (α β : Type) : Type
  | mk : NatOf (T₂ α) → T₂ α β

abbrev InList : List (Type → Type) → Type :=
  fun _ => Nat
/--
error: Missing parameter(s) in occurrence of inductive type: In the expression
  [Foo]
found
  Foo
but expected all parameters to be specified:
  Foo α

Note: All occurrences of an inductive type in the types of its constructors must specify its fixed parameters. Only indices can be omitted in a partial application of the type constructor.
-/
#guard_msgs in
inductive Foo (α : Type) : Type
  | mk : InList [Foo] → Foo α


/-! ## "Mismatched parameter" error -/

/--
error: Mismatched inductive type parameter in
  BadIdx α 0
The provided argument
  0
is not definitionally equal to the expected parameter
  n

Note: The value of parameter `n` must be fixed throughout the inductive declaration. Consider making this parameter an index if it must vary.
-/
#guard_msgs in
inductive BadIdx (α : Type) (n : Nat) : Type
  | mk : BadIdx α 0

/--
error: Mismatched inductive type parameter in
  BadIdx' α 0 k
The provided argument
  0
is not definitionally equal to the expected parameter
  n

Note: The value of parameter `n` must be fixed throughout the inductive declaration. Consider making this parameter an index if it must vary.
-/
#guard_msgs in
inductive BadIdx' (α : Type) (n k : Nat) : Type
  | mk : BadIdx' α 0 k


/-! ## "Mismatched parameter" preempts "missing parameter" -/

/--
error: Mismatched inductive type parameter in
  Bar Nat
The provided argument
  Nat
is not definitionally equal to the expected parameter
  α

Note: The value of parameter `α` must be fixed throughout the inductive declaration. Consider making this parameter an index if it must vary.
-/
#guard_msgs in
inductive Bar (α β : Type) : Type
  | mk : NatOf (Bar Nat) → Bar α β
