
/-!
This file tests the `rfl` tactic:
 * Extensibility
 * Error messages
 * Effect of `with_reducible`
-/

-- First, let's see what `rfl` does:

/--
error: tactic 'rfl' failed, the left-hand side
  false
is not definitionally equal to the right-hand side
  true
⊢ false = true
-/
#guard_msgs in
example : false = true := by rfl

-- Now to `apply_rfl`.

-- A plain reflexive predicate
inductive P : α → α → Prop where | refl : P a a
attribute [refl] P.refl

-- Plain error

/--
error: tactic 'rfl' failed, the left-hand side
  42
is not definitionally equal to the right-hand side
  23
⊢ P 42 23
-/
#guard_msgs in
example : P 42 23 := by apply_rfl

-- Revealing implicit arguments

opaque withImplicitNat {n : Nat} : Nat

/--
error: tactic 'rfl' failed, the left-hand side
  @withImplicitNat 42
is not definitionally equal to the right-hand side
  @withImplicitNat 23
⊢ P withImplicitNat withImplicitNat
-/
#guard_msgs in
example : P (@withImplicitNat 42) (@withImplicitNat 23) := by apply_rfl


-- Exhaustive testing of various combinations:

-- In addition to Eq, HEq and Iff  we test four relations:


-- Defeq to relation `P` at reducible transparency
abbrev Q : α → α → Prop := P

-- Defeq to relation `P` at default transparency
def Q' : α → α → Prop := P

-- No refl attribute
inductive R : α → α → Prop where | refl : R a a


/-
Now we systematically test all relations with
* syntactic equal arguments
* reducibly equal arguments
* semireducibly equal arguments
* nonequal arguments

and all using `apply_rfl` and `with_reducible apply_rfl`
-/


-- Syntactic equal

example : true = true   := by apply_rfl
example : HEq true true := by apply_rfl
example : True ↔ True   := by apply_rfl
example : P true true   := by apply_rfl
example : Q true true   := by apply_rfl
/--
error: tactic 'rfl' failed, no @[refl] lemma registered for relation
  Q'
⊢ Q' true true
-/
#guard_msgs in example : Q' true true  := by apply_rfl -- Error
/--
error: tactic 'rfl' failed, no @[refl] lemma registered for relation
  R
⊢ R true true
-/
#guard_msgs in example : R true true   := by apply_rfl -- Error

example : true = true   := by with_reducible apply_rfl
example : HEq true true := by with_reducible apply_rfl
example : True ↔ True   := by with_reducible apply_rfl
example : P true true   := by with_reducible apply_rfl
example : Q true true   := by with_reducible apply_rfl
/--
error: tactic 'rfl' failed, no @[refl] lemma registered for relation
  Q'
⊢ Q' true true
-/
#guard_msgs in
example : Q' true true  := by with_reducible apply_rfl -- Error
/--
error: tactic 'rfl' failed, no @[refl] lemma registered for relation
  R
⊢ R true true
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
error: tactic 'rfl' failed, no @[refl] lemma registered for relation
  Q'
⊢ Q' true' true'
-/
#guard_msgs in
example : Q' true' true  := by apply_rfl -- Error
/--
error: tactic 'rfl' failed, no @[refl] lemma registered for relation
  R
⊢ R true' true'
-/
#guard_msgs in
example : R true' true   := by apply_rfl -- Error

example : true' = true   := by with_reducible apply_rfl
example : HEq true' true := by with_reducible apply_rfl
example : True' ↔ True   := by with_reducible apply_rfl
example : P true' true   := by with_reducible apply_rfl
example : Q true' true   := by with_reducible apply_rfl -- NB: No error, Q and true' reducible
/--
error: tactic 'rfl' failed, no @[refl] lemma registered for relation
  Q'
⊢ Q' true' true'
-/
#guard_msgs in
example : Q' true' true  := by with_reducible apply_rfl -- Error
/--
error: tactic 'rfl' failed, no @[refl] lemma registered for relation
  R
⊢ R true' true'
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
error: tactic 'rfl' failed, no @[refl] lemma registered for relation
  Q'
⊢ Q' true'' true''
-/
#guard_msgs in
example : Q' true'' true  := by apply_rfl -- Error
/--
error: tactic 'rfl' failed, no @[refl] lemma registered for relation
  R
⊢ R true'' true''
-/
#guard_msgs in
example : R true'' true   := by apply_rfl -- Error

/--
error: tactic 'rfl' failed, the left-hand side
  true''
is not definitionally equal to the right-hand side
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
error: tactic 'rfl' failed, the left-hand side
  True''
is not definitionally equal to the right-hand side
  True
⊢ True'' ↔ True
-/
#guard_msgs in
example : True'' ↔ True   := by with_reducible apply_rfl -- Error
/--
error: tactic 'rfl' failed, the left-hand side
  true''
is not definitionally equal to the right-hand side
  true
⊢ P true'' true
-/
#guard_msgs in
example : P true'' true   := by with_reducible apply_rfl -- Error
/--
error: tactic 'rfl' failed, the left-hand side
  true''
is not definitionally equal to the right-hand side
  true
⊢ Q true'' true
-/
#guard_msgs in
example : Q true'' true   := by with_reducible apply_rfl -- Error
/--
error: tactic 'rfl' failed, the left-hand side
  true''
is not definitionally equal to the right-hand side
  true
⊢ Q' true'' true
-/
#guard_msgs in
example : Q' true'' true  := by with_reducible apply_rfl -- Error
/--
error: tactic 'rfl' failed, the left-hand side
  true''
is not definitionally equal to the right-hand side
  true
⊢ R true'' true
-/
#guard_msgs in
example : R true'' true   := by with_reducible apply_rfl -- Error

-- Unequal
/--
error: tactic 'rfl' failed, the left-hand side
  false
is not definitionally equal to the right-hand side
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
error: tactic 'rfl' failed, the left-hand side
  False
is not definitionally equal to the right-hand side
  True
⊢ False ↔ True
-/
#guard_msgs in
example : False ↔ True   := by apply_rfl -- Error
/--
error: tactic 'rfl' failed, the left-hand side
  false
is not definitionally equal to the right-hand side
  true
⊢ P false true
-/
#guard_msgs in
example : P false true   := by apply_rfl -- Error
/--
error: tactic 'rfl' failed, the left-hand side
  false
is not definitionally equal to the right-hand side
  true
⊢ Q false true
-/
#guard_msgs in
example : Q false true   := by apply_rfl -- Error
/--
error: tactic 'rfl' failed, the left-hand side
  false
is not definitionally equal to the right-hand side
  true
⊢ Q' false true
-/
#guard_msgs in
example : Q' false true  := by apply_rfl -- Error
/--
error: tactic 'rfl' failed, the left-hand side
  false
is not definitionally equal to the right-hand side
  true
⊢ R false true
-/
#guard_msgs in
example : R false true   := by apply_rfl -- Error

/--
error: tactic 'rfl' failed, the left-hand side
  false
is not definitionally equal to the right-hand side
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
error: tactic 'rfl' failed, the left-hand side
  False
is not definitionally equal to the right-hand side
  True
⊢ False ↔ True
-/
#guard_msgs in
example : False ↔ True   := by with_reducible apply_rfl -- Error
/--
error: tactic 'rfl' failed, the left-hand side
  false
is not definitionally equal to the right-hand side
  true
⊢ P false true
-/
#guard_msgs in
example : P false true   := by with_reducible apply_rfl -- Error
/--
error: tactic 'rfl' failed, the left-hand side
  false
is not definitionally equal to the right-hand side
  true
⊢ Q false true
-/
#guard_msgs in
example : Q false true   := by with_reducible apply_rfl -- Error
/--
error: tactic 'rfl' failed, the left-hand side
  false
is not definitionally equal to the right-hand side
  true
⊢ Q' false true
-/
#guard_msgs in
example : Q' false true  := by with_reducible apply_rfl -- Error
/--
error: tactic 'rfl' failed, the left-hand side
  false
is not definitionally equal to the right-hand side
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
error: tactic 'rfl' failed, the left-hand side
  true
is not definitionally equal to the right-hand side
  false
⊢ S true false
-/
#guard_msgs in
example : S true false  := by apply_rfl -- Error
/--
error: tactic 'rfl' failed, the left-hand side
  true
is not definitionally equal to the right-hand side
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
