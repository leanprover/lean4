/-!
The (attribute-extensible) `rfl` tactic only unfolds the goal with reducible transparency to look
for a relation which may have a `refl` lemma associated with it. But historically, `rfl` also
invoked `eq_refl`, which more aggressively unfolds. This checks that this still works.
-/

def Foo (a b : Nat) : Prop := a = b

/--
error: tactic 'rfl' failed, no @[refl] lemma registered for relation
  Foo
⊢ Foo 1 1
-/
#guard_msgs in
example : Foo 1 1 := by
  apply_rfl


#guard_msgs in
example : Foo 1 1 := by
  eq_refl

#guard_msgs in
example : Foo 1 1 := by
  rfl
