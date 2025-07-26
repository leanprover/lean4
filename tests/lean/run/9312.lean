/-!
# Projections on types without fields

https://github.com/leanprover/lean4/issues/9312

Ensures that a suitable error message is displayed when attempting to project from a type that has
no fields.
-/

structure MyEmpty where

/--
error: Invalid projection: Projections are not supported on this type because it has no fields
  { }
has type
  MyEmpty
-/
#guard_msgs in
#check (MyEmpty.mk).1

inductive T where
  | a

/--
error: Invalid projection: Projections are not supported on this type because it has no fields
  T.a
has type
  T
-/
#guard_msgs in
#check (T.a).1
