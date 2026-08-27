/-!
# Validation of `Repr Empty` instance

While it may seem unnecessary to have Repr, it prevents the automatic derivation
of Repr for other types when `Empty` is used as a type parameter.

This is a simplified version of an example from the "Functional Programming in Lean" book.
The Empty type is used to exclude the `other` constructor from the `Prim` type.
-/

inductive Prim (special : Type) where
  | plus
  | minus
  | other : special → Prim special
deriving Repr

/-!
Check that both Repr's work
-/

/-- info: Prim.plus -/
#guard_msgs in
open Prim in
#eval (plus : Prim Int)

/-- info: Prim.minus -/
#guard_msgs in
open Prim in
#eval (minus : Prim Empty)
