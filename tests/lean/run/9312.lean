/-!
# Projections on types without fields

https://github.com/leanprover/lean4/issues/9312

Ensures that a suitable error message is displayed when attempting to project from a type that has
no fields.
-/

structure MyEmpty where

/--
error: Invalid projection: Projection operates on structure-like types with fields. The expression
  { }
has type `MyEmpty` which has no fields.
-/
#guard_msgs in
#check (MyEmpty.mk).1

inductive T where
  | a

/--
error: Invalid projection: Projection operates on structure-like types with fields. The expression
  T.a
has type `T` which has no fields.
-/
#guard_msgs in
#check (T.a).1
