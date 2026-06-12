/-!
# Dotted function notation can handle `@` and universe levels
-/

set_option warn.sorry false
set_option linter.deprecated true
set_option pp.mvars.anonymous false

/-!
Explicit `@`
-/
/-- info: [] : List Nat -/
#guard_msgs in #check (@.nil Nat : List _)

/-!
Explicit `@` disables implicit lambda
-/
/--
error: Type mismatch
  @List.nil
has type
  {α : Type _} → List α
but is expected to have type
  List ?_
-/
#guard_msgs in #check (@.nil : List _)

/-!
Universe levels.
-/
example : List Nat := .nil.{0}

/--
error: Type mismatch
  []
has type
  List.{1} ?_
of sort `Type 1` but is expected to have type
  List.{0} Nat
of sort `Type`
-/
#guard_msgs in
example : List Nat := .nil.{1}

/-- error: too many explicit universe levels for `List.nil` -/
#guard_msgs in
example : List Nat := .nil.{0,0}

/-!
Explicit plus universe levels also disables implicit lambda
-/
/--
error: Type mismatch
  @List.nil
has type
  {α : Type} → List α
of sort `Type 1` but is expected to have type
  List Nat
of sort `Type`
-/
#guard_msgs in example : List Nat := @.nil.{0}

/-!
Example of `@` from Floris van Doorn at https://github.com/leanprover/lean4/issues/10984
-/
example {α : Type} (f : ∀ {α}, List α → List α) : f (@.nil α) = .nil := sorry

/-!
Example of `@` plus universe levels adapted from https://github.com/leanprover/lean4/issues/10984
-/
example {α : Type u} (f : ∀ {α}, List α → List α) : f (@.nil.{u} α) = .nil := sorry

/-!
Example from Arthur Adjedj at https://github.com/leanprover/lean4/issues/8743
-/
/-- info: [2] : List Nat -/
#guard_msgs in #check (List.cons.{0} 2 [] : List Nat)
/-- info: [2] : List Nat -/
#guard_msgs in #check (.cons.{0} 2 [] : List Nat)

/--
error: Type mismatch
  [2]
has type
  List.{1} ?_
of sort `Type 1` but is expected to have type
  List.{0} Nat
of sort `Type`
-/
#guard_msgs in #check (.cons.{1} 2 [] : List Nat)

/-!
Regression test: This used to give a deprecation warning on the first `#check`.
-/
def MyNS1.List.nil' : List Nat := []
@[deprecated MyNS1.List.nil' (since := "forever")] def MyNS2.List.nil' : List Int := []

/-- info: MyNS1.List.nil' : List Nat -/
#guard_msgs in
open MyNS1 MyNS2 in #check (.nil' : List Nat)

/--
warning: `MyNS2.List.nil'` has been deprecated: Use `MyNS1.List.nil'` instead

Note: The updated constant has a different type:
  List Nat
instead of
  List Int

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.nil'` to `MyNS1.List.nil' x`).
---
info: MyNS2.List.nil' : List Int
-/
#guard_msgs in
open MyNS1 MyNS2 in #check (.nil' : List Int)
