
/-!
This file tests the `rfl` tactic:
 * Extensibility
 * Error messages
 * Effect of `with_reducible`
-/

/--
error: The rfl tactic failed. Possible reasons:
- The goal is not a reflexive relation (neither `=` nor a relation with a @[refl] lemma).
- The arguments of the relation are not equal.
Try using the reflexivity lemma for your relation explicitly, e.g. `exact Eq.refl _` or
`exact HEq.rfl` etc.
⊢ false = true
-/
#guard_msgs in
example : false = true := by rfl

-- Setup

inductive P : α → α → Prop where | refl : P a a
attribute [refl] P.refl

-- Defeq to relation `P` at reducible transparency
abbrev Q : α → α → Prop := P
-- Defeq to relation `P` at default transparency
def Q' : α → α → Prop := P

-- No refl attribute
inductive R : α → α → Prop where | refl : R a a

-- Syntactic equal

example : true = true   := by apply_rfl
example : HEq true true := by apply_rfl
example : True ↔ True   := by apply_rfl
example : P true true   := by apply_rfl
example : Q true true   := by apply_rfl
/--
error: rfl failed, no @[refl] lemma registered for relation
  Q'
-/
#guard_msgs in example : Q' true true  := by apply_rfl -- Error
/--
error: rfl failed, no @[refl] lemma registered for relation
  R
-/
#guard_msgs in example : R true true   := by apply_rfl -- Error

example : true = true   := by with_reducible apply_rfl
example : HEq true true := by with_reducible apply_rfl
example : True ↔ True   := by with_reducible apply_rfl
example : P true true   := by with_reducible apply_rfl
example : Q true true   := by with_reducible apply_rfl
/--
error: rfl failed, no @[refl] lemma registered for relation
  Q'
-/
#guard_msgs in
example : Q' true true  := by with_reducible apply_rfl -- Error
/--
error: rfl failed, no @[refl] lemma registered for relation
  R
-/
#guard_msgs in
example : R true true   := by with_reducible apply_rfl -- Error

-- Reducibly equal

abbrev true' := true
abbrev True' := True

example : true' = true   := by apply_rfl
example : HEq true' true := by apply_rfl
example : True' ↔ True   := by apply_rfl
example : P true' true   := by apply_rfl
example : Q true' true   := by apply_rfl
/--
error: rfl failed, no @[refl] lemma registered for relation
  Q'
-/
#guard_msgs in
example : Q' true' true  := by apply_rfl -- Error
/--
error: rfl failed, no @[refl] lemma registered for relation
  R
-/
#guard_msgs in
example : R true' true   := by apply_rfl -- Error

example : true' = true   := by with_reducible apply_rfl
example : HEq true' true := by with_reducible apply_rfl
example : True' ↔ True   := by with_reducible apply_rfl
example : P true' true   := by with_reducible apply_rfl
example : Q true' true   := by with_reducible apply_rfl -- NB: No error, Q and true' reducible
/--
error: rfl failed, no @[refl] lemma registered for relation
  Q'
-/
#guard_msgs in
example : Q' true' true  := by with_reducible apply_rfl -- Error
/--
error: rfl failed, no @[refl] lemma registered for relation
  R
-/
#guard_msgs in
example : R true' true   := by with_reducible apply_rfl -- Error

-- Equal at default transparency only

def true'' := true
def True'' := True

example : true'' = true   := by apply_rfl
example : HEq true'' true := by apply_rfl
example : True'' ↔ True   := by apply_rfl
example : P true'' true   := by apply_rfl
example : Q true'' true   := by apply_rfl
/--
error: rfl failed, no @[refl] lemma registered for relation
  Q'
-/
#guard_msgs in
example : Q' true'' true  := by apply_rfl -- Error
/--
error: rfl failed, no @[refl] lemma registered for relation
  R
-/
#guard_msgs in
example : R true'' true   := by apply_rfl -- Error

/--
error: tactic 'rfl' failed, The lhs
  true''
is not definitionally equal to rhs
  true
⊢ true'' = true
-/
#guard_msgs in
example : true'' = true   := by with_reducible apply_rfl -- Error
/--
error: tactic 'apply' failed, failed to unify
  @HEq ?α ?a ?α ?a
with
  @HEq Bool true'' Bool true
⊢ HEq true'' true
-/
#guard_msgs in
example : HEq true'' true := by with_reducible apply_rfl -- Error
/--
error: tactic 'rfl' failed, The lhs
  True''
is not definitionally equal to rhs
  True
⊢ True'' ↔ True
-/
#guard_msgs in
example : True'' ↔ True   := by with_reducible apply_rfl -- Error
/--
error: tactic 'rfl' failed, The lhs
  true''
is not definitionally equal to rhs
  true
⊢ P true'' true
-/
#guard_msgs in
example : P true'' true   := by with_reducible apply_rfl -- Error
/--
error: tactic 'rfl' failed, The lhs
  true''
is not definitionally equal to rhs
  true
⊢ Q true'' true
-/
#guard_msgs in
example : Q true'' true   := by with_reducible apply_rfl -- Error
/--
error: tactic 'rfl' failed, The lhs
  true''
is not definitionally equal to rhs
  true
⊢ Q' true'' true
-/
#guard_msgs in
example : Q' true'' true  := by with_reducible apply_rfl -- Error
/--
error: tactic 'rfl' failed, The lhs
  true''
is not definitionally equal to rhs
  true
⊢ R true'' true
-/
#guard_msgs in
example : R true'' true   := by with_reducible apply_rfl -- Error

-- Unequal
/--
error: tactic 'rfl' failed, The lhs
  false
is not definitionally equal to rhs
  true
⊢ false = true
-/
#guard_msgs in
example : false = true   := by apply_rfl -- Error
/--
error: tactic 'apply' failed, failed to unify
  HEq ?a ?a
with
  HEq false true
⊢ HEq false true
-/
#guard_msgs in
example : HEq false true := by apply_rfl -- Error
/--
error: tactic 'rfl' failed, The lhs
  False
is not definitionally equal to rhs
  True
⊢ False ↔ True
-/
#guard_msgs in
example : False ↔ True   := by apply_rfl -- Error
/--
error: tactic 'rfl' failed, The lhs
  false
is not definitionally equal to rhs
  true
⊢ P false true
-/
#guard_msgs in
example : P false true   := by apply_rfl -- Error
/--
error: tactic 'rfl' failed, The lhs
  false
is not definitionally equal to rhs
  true
⊢ Q false true
-/
#guard_msgs in
example : Q false true   := by apply_rfl -- Error
/--
error: tactic 'rfl' failed, The lhs
  false
is not definitionally equal to rhs
  true
⊢ Q' false true
-/
#guard_msgs in
example : Q' false true  := by apply_rfl -- Error
/--
error: tactic 'rfl' failed, The lhs
  false
is not definitionally equal to rhs
  true
⊢ R false true
-/
#guard_msgs in
example : R false true   := by apply_rfl -- Error

/--
error: tactic 'rfl' failed, The lhs
  false
is not definitionally equal to rhs
  true
⊢ false = true
-/
#guard_msgs in
example : false = true   := by with_reducible apply_rfl -- Error
/--
error: tactic 'apply' failed, failed to unify
  HEq ?a ?a
with
  HEq false true
⊢ HEq false true
-/
#guard_msgs in
example : HEq false true := by with_reducible apply_rfl -- Error
/--
error: tactic 'rfl' failed, The lhs
  False
is not definitionally equal to rhs
  True
⊢ False ↔ True
-/
#guard_msgs in
example : False ↔ True   := by with_reducible apply_rfl -- Error
/--
error: tactic 'rfl' failed, The lhs
  false
is not definitionally equal to rhs
  true
⊢ P false true
-/
#guard_msgs in
example : P false true   := by with_reducible apply_rfl -- Error
/--
error: tactic 'rfl' failed, The lhs
  false
is not definitionally equal to rhs
  true
⊢ Q false true
-/
#guard_msgs in
example : Q false true   := by with_reducible apply_rfl -- Error
/--
error: tactic 'rfl' failed, The lhs
  false
is not definitionally equal to rhs
  true
⊢ Q' false true
-/
#guard_msgs in
example : Q' false true  := by with_reducible apply_rfl -- Error
/--
error: tactic 'rfl' failed, The lhs
  false
is not definitionally equal to rhs
  true
⊢ R false true
-/
#guard_msgs in
example : R false true   := by with_reducible apply_rfl -- Error

-- Inheterogeneous unequal

/--
error: tactic 'apply' failed, failed to unify
  HEq ?a ?a
with
  HEq true 1
⊢ HEq true 1
-/
#guard_msgs in
example : HEq true 1 := by apply_rfl -- Error
/--
error: tactic 'apply' failed, failed to unify
  HEq ?a ?a
with
  HEq true 1
⊢ HEq true 1
-/
#guard_msgs in
example : HEq true 1 := by with_reducible apply_rfl -- Error

-- Rfl lemma with side condition:
-- Error message should show left-over goal

inductive S : Bool → Bool → Prop where | refl : a = true → S a a
attribute [refl] S.refl
/--
error: tactic 'rfl' failed, The lhs
  true
is not definitionally equal to rhs
  false
⊢ S true false
-/
#guard_msgs in
example : S true false  := by apply_rfl -- Error
/--
error: tactic 'rfl' failed, The lhs
  true
is not definitionally equal to rhs
  false
⊢ S true false
-/
#guard_msgs in
example : S true false  := by with_reducible apply_rfl -- Error
/--
error: unsolved goals
case a
⊢ true = true
-/
#guard_msgs in
example : S true true   := by apply_rfl -- Error (left-over goal)
/--
error: unsolved goals
case a
⊢ true = true
-/
#guard_msgs in
example : S true true   := by with_reducible apply_rfl -- Error (left-over goal)
/--
error: unsolved goals
case a
⊢ false = true
-/
#guard_msgs in
example : S false false := by apply_rfl -- Error (left-over goal)
/--
error: unsolved goals
case a
⊢ false = true
-/
#guard_msgs in
example : S false false := by with_reducible apply_rfl -- Error (left-over goal)
