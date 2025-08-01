
set_option pp.mvars.levels false

/-!
This file tests the `rfl` tactic:
 * Extensibility
 * Error messages
 * Effect of `with_reducible`
-/

set_option pp.mvars.levels false

-- First, let's see what `rfl` does:

/--
error: Tactic `rfl` failed: The left-hand side
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
error: Tactic `rfl` failed: The left-hand side
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
error: Tactic `rfl` failed: The left-hand side
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
example : true ≍ true := by apply_rfl
example : True ↔ True   := by apply_rfl
example : P true true   := by apply_rfl
example : Q true true   := by apply_rfl
/--
error: Tactic `rfl` failed: No `[refl]` lemma registered for relation
  Q'

Hint: Add the `[refl]` attribute to reflexivity lemmas for `Q'` to use this tactic

⊢ Q' true true
-/
#guard_msgs in example : Q' true true  := by apply_rfl -- Error
/--
error: Tactic `rfl` failed: No `[refl]` lemma registered for relation
  R

Hint: Add the `[refl]` attribute to reflexivity lemmas for `R` to use this tactic

⊢ R true true
-/
#guard_msgs in example : R true true   := by apply_rfl -- Error

example : true = true   := by with_reducible apply_rfl
example : true ≍ true := by with_reducible apply_rfl
example : True ↔ True   := by with_reducible apply_rfl
example : P true true   := by with_reducible apply_rfl
example : Q true true   := by with_reducible apply_rfl
/--
error: Tactic `rfl` failed: No `[refl]` lemma registered for relation
  Q'

Hint: Add the `[refl]` attribute to reflexivity lemmas for `Q'` to use this tactic

⊢ Q' true true
-/
#guard_msgs in
example : Q' true true  := by with_reducible apply_rfl -- Error
/--
error: Tactic `rfl` failed: No `[refl]` lemma registered for relation
  R

Hint: Add the `[refl]` attribute to reflexivity lemmas for `R` to use this tactic

⊢ R true true
-/
#guard_msgs in
example : R true true   := by with_reducible apply_rfl -- Error

-- Reducibly equal

abbrev true' := true
abbrev True' := True

example : true' = true   := by apply_rfl
example : true' ≍ true := by apply_rfl
example : True' ↔ True   := by apply_rfl
example : P true' true   := by apply_rfl
example : Q true' true   := by apply_rfl
/--
error: Tactic `rfl` failed: No `[refl]` lemma registered for relation
  Q'

Hint: Add the `[refl]` attribute to reflexivity lemmas for `Q'` to use this tactic

⊢ Q' true' true'
-/
#guard_msgs in
example : Q' true' true  := by apply_rfl -- Error
/--
error: Tactic `rfl` failed: No `[refl]` lemma registered for relation
  R

Hint: Add the `[refl]` attribute to reflexivity lemmas for `R` to use this tactic

⊢ R true' true'
-/
#guard_msgs in
example : R true' true   := by apply_rfl -- Error

example : true' = true   := by with_reducible apply_rfl
example : true' ≍ true := by with_reducible apply_rfl
example : True' ↔ True   := by with_reducible apply_rfl
example : P true' true   := by with_reducible apply_rfl
example : Q true' true   := by with_reducible apply_rfl -- NB: No error, Q and true' reducible
/--
error: Tactic `rfl` failed: No `[refl]` lemma registered for relation
  Q'

Hint: Add the `[refl]` attribute to reflexivity lemmas for `Q'` to use this tactic

⊢ Q' true' true'
-/
#guard_msgs in
example : Q' true' true  := by with_reducible apply_rfl -- Error
/--
error: Tactic `rfl` failed: No `[refl]` lemma registered for relation
  R

Hint: Add the `[refl]` attribute to reflexivity lemmas for `R` to use this tactic

⊢ R true' true'
-/
#guard_msgs in
example : R true' true   := by with_reducible apply_rfl -- Error

-- Equal at default transparency only

def true'' := true
def True'' := True

example : true'' = true   := by apply_rfl
example : true'' ≍ true := by apply_rfl
example : True'' ↔ True   := by apply_rfl
example : P true'' true   := by apply_rfl
example : Q true'' true   := by apply_rfl
/--
error: Tactic `rfl` failed: No `[refl]` lemma registered for relation
  Q'

Hint: Add the `[refl]` attribute to reflexivity lemmas for `Q'` to use this tactic

⊢ Q' true'' true''
-/
#guard_msgs in
example : Q' true'' true  := by apply_rfl -- Error
/--
error: Tactic `rfl` failed: No `[refl]` lemma registered for relation
  R

Hint: Add the `[refl]` attribute to reflexivity lemmas for `R` to use this tactic

⊢ R true'' true''
-/
#guard_msgs in
example : R true'' true   := by apply_rfl -- Error

/--
error: Tactic `rfl` failed: The left-hand side
  true''
is not definitionally equal to the right-hand side
  true

⊢ true'' = true
-/
#guard_msgs in
example : true'' = true   := by with_reducible apply_rfl -- Error


/--
error: Tactic `apply` failed: could not unify the conclusion of 'HEq.refl'
  @HEq ?α ?a ?α ?a
with the goal
  @HEq Bool true'' Bool true

Note: The full type of 'HEq.refl' is
  ∀ {α : Sort _} (a : α), a ≍ a

⊢ true'' ≍ true
-/
#guard_msgs in
example : true'' ≍ true := by with_reducible apply_rfl -- Error
/--
error: Tactic `rfl` failed: The left-hand side
  True''
is not definitionally equal to the right-hand side
  True

⊢ True'' ↔ True
-/
#guard_msgs in
example : True'' ↔ True   := by with_reducible apply_rfl -- Error
/--
error: Tactic `rfl` failed: The left-hand side
  true''
is not definitionally equal to the right-hand side
  true

⊢ P true'' true
-/
#guard_msgs in
example : P true'' true   := by with_reducible apply_rfl -- Error
/--
error: Tactic `rfl` failed: The left-hand side
  true''
is not definitionally equal to the right-hand side
  true

⊢ Q true'' true
-/
#guard_msgs in
example : Q true'' true   := by with_reducible apply_rfl -- Error
/--
error: Tactic `rfl` failed: The left-hand side
  true''
is not definitionally equal to the right-hand side
  true

⊢ Q' true'' true
-/
#guard_msgs in
example : Q' true'' true  := by with_reducible apply_rfl -- Error
/--
error: Tactic `rfl` failed: The left-hand side
  true''
is not definitionally equal to the right-hand side
  true

⊢ R true'' true
-/
#guard_msgs in
example : R true'' true   := by with_reducible apply_rfl -- Error

-- Unequal
/--
error: Tactic `rfl` failed: The left-hand side
  false
is not definitionally equal to the right-hand side
  true

⊢ false = true
-/
#guard_msgs in
example : false = true   := by apply_rfl -- Error
/--
error: Tactic `apply` failed: could not unify the conclusion of 'HEq.refl'
  ?a ≍ ?a
with the goal
  false ≍ true

Note: The full type of 'HEq.refl' is
  ∀ {α : Sort _} (a : α), a ≍ a

⊢ false ≍ true
-/
#guard_msgs in
example : false ≍ true := by apply_rfl -- Error
/--
error: Tactic `rfl` failed: The left-hand side
  False
is not definitionally equal to the right-hand side
  True

⊢ False ↔ True
-/
#guard_msgs in
example : False ↔ True   := by apply_rfl -- Error
/--
error: Tactic `rfl` failed: The left-hand side
  false
is not definitionally equal to the right-hand side
  true

⊢ P false true
-/
#guard_msgs in
example : P false true   := by apply_rfl -- Error
/--
error: Tactic `rfl` failed: The left-hand side
  false
is not definitionally equal to the right-hand side
  true

⊢ Q false true
-/
#guard_msgs in
example : Q false true   := by apply_rfl -- Error
/--
error: Tactic `rfl` failed: The left-hand side
  false
is not definitionally equal to the right-hand side
  true

⊢ Q' false true
-/
#guard_msgs in
example : Q' false true  := by apply_rfl -- Error
/--
error: Tactic `rfl` failed: The left-hand side
  false
is not definitionally equal to the right-hand side
  true

⊢ R false true
-/
#guard_msgs in
example : R false true   := by apply_rfl -- Error

/--
error: Tactic `rfl` failed: The left-hand side
  false
is not definitionally equal to the right-hand side
  true

⊢ false = true
-/
#guard_msgs in
example : false = true   := by with_reducible apply_rfl -- Error
/--
error: Tactic `apply` failed: could not unify the conclusion of 'HEq.refl'
  ?a ≍ ?a
with the goal
  false ≍ true

Note: The full type of 'HEq.refl' is
  ∀ {α : Sort _} (a : α), a ≍ a

⊢ false ≍ true
-/
#guard_msgs in
example : false ≍ true := by with_reducible apply_rfl -- Error
/--
error: Tactic `rfl` failed: The left-hand side
  False
is not definitionally equal to the right-hand side
  True

⊢ False ↔ True
-/
#guard_msgs in
example : False ↔ True   := by with_reducible apply_rfl -- Error
/--
error: Tactic `rfl` failed: The left-hand side
  false
is not definitionally equal to the right-hand side
  true

⊢ P false true
-/
#guard_msgs in
example : P false true   := by with_reducible apply_rfl -- Error
/--
error: Tactic `rfl` failed: The left-hand side
  false
is not definitionally equal to the right-hand side
  true

⊢ Q false true
-/
#guard_msgs in
example : Q false true   := by with_reducible apply_rfl -- Error
/--
error: Tactic `rfl` failed: The left-hand side
  false
is not definitionally equal to the right-hand side
  true

⊢ Q' false true
-/
#guard_msgs in
example : Q' false true  := by with_reducible apply_rfl -- Error
/--
error: Tactic `rfl` failed: The left-hand side
  false
is not definitionally equal to the right-hand side
  true

⊢ R false true
-/
#guard_msgs in
example : R false true   := by with_reducible apply_rfl -- Error

-- Inheterogeneous unequal

/--
error: Tactic `apply` failed: could not unify the conclusion of 'HEq.refl'
  ?a ≍ ?a
with the goal
  true ≍ 1

Note: The full type of 'HEq.refl' is
  ∀ {α : Sort _} (a : α), a ≍ a

⊢ true ≍ 1
-/
#guard_msgs in
example : true ≍ 1 := by apply_rfl -- Error
/--
error: Tactic `apply` failed: could not unify the conclusion of 'HEq.refl'
  ?a ≍ ?a
with the goal
  true ≍ 1

Note: The full type of 'HEq.refl' is
  ∀ {α : Sort _} (a : α), a ≍ a

⊢ true ≍ 1
-/
#guard_msgs in
example : true ≍ 1 := by with_reducible apply_rfl -- Error

-- Rfl lemma with side condition:
-- Error message should show left-over goal

inductive S : Bool → Bool → Prop where | refl : a = true → S a a
attribute [refl] S.refl
/--
error: Tactic `rfl` failed: The left-hand side
  true
is not definitionally equal to the right-hand side
  false

⊢ S true false
-/
#guard_msgs in
example : S true false  := by apply_rfl -- Error
/--
error: Tactic `rfl` failed: The left-hand side
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
