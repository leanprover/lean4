/--
error: tactic 'apply' failed, could not unify the type of `x`
  PUnit.{1}
with the goal
  PUnit.{0}
x : PUnit
⊢ PUnit
-/
#guard_msgs in
example (x : PUnit.{1}) : PUnit.{0} := by
  apply x

/--
error: type mismatch
  x
has type
  PUnit.{1} : Type
but is expected to have type
  PUnit.{0} : Prop
-/
#guard_msgs in
example (x : PUnit.{1}) : PUnit.{0} :=
  x

/--
error: tactic 'rfl' failed, the left-hand side
  ∀ (x : PUnit.{1}), True
is not definitionally equal to the right-hand side
  ∀ (x : PUnit.{2}), True
⊢ (∀ (x : PUnit), True) ↔ ∀ (x : PUnit), True
-/
#guard_msgs in
example : (∀ _ : PUnit.{1}, True) ↔ ∀ _ : PUnit.{2}, True := by
  rfl

inductive Test where
  | mk (x : Prop)

/--
error: tactic 'rfl' failed, the left-hand side
  (Test.mk (∀ (x : PUnit.{1}), True)).1
is not definitionally equal to the right-hand side
  (Test.mk (∀ (x : PUnit.{2}), True)).1
⊢ (Test.mk (∀ (x : PUnit), True)).1 = (Test.mk (∀ (x : PUnit), True)).1
-/
#guard_msgs in
example : (Test.mk (∀ _ : PUnit.{1}, True)).1 = (Test.mk (∀ _ : PUnit.{2}, True)).1 := by
  rfl
