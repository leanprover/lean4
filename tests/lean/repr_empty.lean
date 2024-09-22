/-!
This test validates the Repr instance for `Empty`.

While it may seem unnecessary to have Repr, it prevents the automatic derivation
of Repr for other types when `Empty` is used as a type parameter.

This is a simplified version of an example from the "Functional Programming in Lean" book.
The Empty type is used to exlude the `other` constructor from the `Prim` type.
-/

inductive Prim (special : Type) where
  | plus
  | minus
  | other : special → Prim special
deriving Repr

-- Check that both Repr's work
open Prim in
#eval (plus: Prim Int)

open Prim in
#eval (minus: Prim Empty)
