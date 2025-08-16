import Lean
/-!
This test exercises the elaborator's positivity check for inductive data types, and related
checks around nested induction.
-/

/--
error: In argument #1 of constructor Bad.mk:
  Non-positive occurrence of inductive type `Bad`
-/
#guard_msgs in
inductive Bad where
  | mk : (Bad → Bad) → Bad

/--
error: In argument #1 of constructor Bad1.mk:
  Non-positive occurrence of inductive type `Bad2`
-/
#guard_msgs in
mutual
inductive Bad1 where
  | mk : (Bad2 → Bad2) → Bad1
inductive Bad2 where
  | mk : (Bad1 → Bad1) → Bad2
end

inductive Ok1 where
  | mk : id Ok1 → Ok1


axiom T : Type → Type

/--
error: In argument #1 of constructor Bad3.mk:
  Non-positive occurrence of inductive type `Bad3`: Nested occurrences can only occur in inductive types, not in `T`.
-/
#guard_msgs in
inductive Bad3 where
  | mk : T Bad3 → Bad3

inductive Ok2 where
  | mk : List Ok2 → Ok2

/--
error: Mismatched inductive type parameter in
  Bad4 (α × α)
The provided argument
  α × α
is not definitionally equal to the expected parameter
  α

Note: The value of parameter 'α' must be fixed throughout the inductive declaration. Consider making this parameter an index if it must vary.
-/
#guard_msgs in
inductive Bad4 (α : Type) : Type where
  | mk : Bad4 (α × α) → Bad4 α

inductive Nest5 (f : Nat → Type) where
  | mk : f 5 → Nest5 f

inductive Ok5 : Nat → Type where
  | mk : Nest5 Ok5 → Ok5 n

inductive Nest6 (f : Nat → Type) where
  | mk : f n → Nest6 f

inductive Ok6 : Nat → Type where
  | mk : Nest6 Ok6 → Ok6 n

inductive Nest7 (n : Nat) (f : Nat → Type) where
  | mk : f n → Nest7 n f

/--
error: In argument #2 of constructor Bad7.mk:
  Nested inductive datatype parameters cannot contain local variable `n`.
-/
#guard_msgs in
inductive Bad7 : Nat → Type where
  | mk : Nest7 n Bad7 → Bad7 n

inductive Good7 (n : Nat) : Nat → Type where
  | mk : Nest7 n (Good7 n) → Good7 n n

inductive Nest8 (α : Type) : (β : Type) → Type  where
  | mk : α → Nest8 α Bool

inductive Ok8 : Type where
  | mk : Nest8 Ok8 Unit → Ok8

/--
error: In argument #1 of constructor Bad8.mk:
  Invalid occurrence of inductive type `Bad8`, must not occur in index of `Nest8`
-/
#guard_msgs in
inductive Bad8 : Type where
  | mk : Nest8 Unit Bad8 → Bad8

inductive Nest9 (α : Type) : Type  where
  | mk : (α → α) → Nest9 α

/--
error: In argument #1 of constructor Bad9.mk:
  Invalid occurrence of inductive type `Bad9`, parameter #1 of `Nest9` is not positive.
  ⏎
  Note: That parameter is not positive:
    Non-positive occurrence of parameter `α` in type of Nest9.mk
-/
#guard_msgs in
inductive Bad9 where
  | mk : Nest9 Bad9 → Bad9


inductive Nest10 (α : Type) : Type  where
  | mk : α  → Nest10 α

inductive Ok10 where
  | mk : Nest10 (Bool -> Ok10) → Ok10

inductive Nest11 (α : Bool → Type) : Type  where
  | mk : α true → Nest11 α

inductive Ok11  : Bool → Type where
  | mk : Nest11 Ok11 → Ok11 true

/-
The following code tried to check if positivity checking blows up exponentially
with nested types, but it still seems fast compared to other things happening, so
this test does not actually blow up as desired.
We still memoize the queries, as can manually be checked using `set_option trace.Elab.inductive
true`.
-/

-- set_option trace.Elab.inductive true
-- set_option debug.inductiveCheckPositivity false

inductive Ok12a α where | mk : α → Ok12a α
inductive Ok12b α where | mk : Ok12a α → Ok12a α → Ok12a α → Ok12a α → Ok12a α → Ok12a α →  Ok12b α
inductive Ok12c α where | mk : Ok12b α → Ok12b α → Ok12b α → Ok12b α → Ok12b α → Ok12b α →  Ok12c α
inductive Ok12d α where | mk : Ok12c α → Ok12c α → Ok12c α → Ok12c α → Ok12c α → Ok12c α →  Ok12d α
inductive Ok12e α where | mk : Ok12d α → Ok12d α → Ok12d α → Ok12d α → Ok12d α → Ok12d α →  Ok12e α
inductive Ok12f α where | mk : Ok12e α → Ok12e α → Ok12e α → Ok12e α → Ok12e α → Ok12e α →  Ok12f α

inductive Ok12 where | mk : Ok12c Ok12 → Ok12
-- inductive Ok12 where | mk : Ok12f Ok12 → Ok12
