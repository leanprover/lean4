/-!
# Tests of universe constraint testing in the `inductive` command
-/

set_option pp.mvars false
set_option pp.universes true

/-!
Given the resultant type, infer that the `x` parameter is `Type`.
-/
inductive T0 : Type where
  | mk (x : PUnit.{_+1})
/-- info: T0.mk (x : PUnit.{1}) : T0 -/
#guard_msgs in #check T0.mk

/-!
Given the resultant type, infer that the `x` parameter is `Type` as well.
-/
inductive T1 : Type where
  | mk (x : PUnit.{_+1} × PUnit.{_+1})
/-- info: T1.mk (x : Prod.{0, 0} PUnit.{1} PUnit.{1}) : T1 -/
#guard_msgs in #check T1.mk

/-!
Given the resultant type is `Prop`, do not do this inference. Get two universe levels.
-/
inductive T3 : Prop where
  | mk (x : PUnit.{_+1} × PUnit.{_+1})
/-- info: T3.mk.{u_1, u_2} (x : Prod.{u_1, u_2} PUnit.{u_1 + 1} PUnit.{u_2 + 1}) : T3.{u_1, u_2} -/
#guard_msgs in #check T3.mk

/-!
Given the resultant type, fail to infer a level for `PUnit` if there's not a unique solution.
-/
/--
error: invalid universe level in constructor 'E0.mk', parameter 'x' has type
  PUnit.{u_1}
at universe level
  u_1
which is not less than or equal to the inductive type's resulting universe level
  1
-/
#guard_msgs in
inductive E0 : Type where
  | mk (x : PUnit)

/-!
Given the resultant type, fail to infer a level for `PUnit` if there's not a unique solution.
-/
/--
error: invalid universe level in constructor 'E1.mk', parameter 'x' has type
  Prod.{u_1, u_2} PUnit.{u_1 + 1} PUnit.{u_2 + 1}
at universe level
  max (u_1+1) (u_2+1)
which is not less than or equal to the inductive type's resulting universe level
  2
-/
#guard_msgs in
inductive E1 : Type 1 where
  | mk (x : PUnit × PUnit)

/-!
`Sort` polymorphism is not allowed.
-/
/--
error: invalid universe polymorphic resulting type, the resulting universe is not 'Prop', but it may be 'Prop' for some parameter values:
  Sort u
Possible solution: use levels of the form 'max 1 _' or '_ + 1' to ensure the universe is of the form 'Type _'.
-/
#guard_msgs in
inductive P (α : Sort u) : Sort u where
  | mk (x : α)

/-!
Errors for `structure` are specialized to talking about fields.
-/
/--
error: invalid universe level for field 'α', has type
  Type
at universe level
  2
which is not less than or equal to the structure's resulting universe level
  1
-/
#guard_msgs in
structure A : Type where
  α : Type

/-!
Errors for `structure` talk about parent projection fields too.
(Note: it could easily point to `A'` and say the error is field `α`.)
-/
structure A' where
  α : Type
/--
error: invalid universe level for field 'toA'', has type
  A'
at universe level
  2
which is not less than or equal to the structure's resulting universe level
  1
-/
#guard_msgs in
structure B : Type extends A'
