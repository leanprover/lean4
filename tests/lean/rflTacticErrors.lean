
/-!
This file tests the `rfl` tactic:
 * Extensibility
 * Error messages
 * Effect of `with_reducible`
-/

-- Remove the following once `apply_rfl` and `rfl` are merged
-- Until then: Note the horrible error message!
example : false = true   := by rfl

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
example : Q' true true  := by apply_rfl -- Error
example : R true true   := by apply_rfl -- Error

example : true = true   := by with_reducible apply_rfl
example : HEq true true := by with_reducible apply_rfl
example : True ↔ True   := by with_reducible apply_rfl
example : P true true   := by with_reducible apply_rfl
example : Q true true   := by with_reducible apply_rfl
example : Q' true true  := by with_reducible apply_rfl -- Error
example : R true true   := by with_reducible apply_rfl -- Error

-- Reducibly equal

abbrev true' := true
abbrev True' := True

example : true' = true   := by apply_rfl
example : HEq true' true := by apply_rfl
example : True' ↔ True   := by apply_rfl
example : P true' true   := by apply_rfl
example : Q true' true   := by apply_rfl
example : Q' true' true  := by apply_rfl -- Error
example : R true' true   := by apply_rfl -- Error

example : true' = true   := by with_reducible apply_rfl
example : HEq true' true := by with_reducible apply_rfl
example : True' ↔ True   := by with_reducible apply_rfl
example : P true' true   := by with_reducible apply_rfl
example : Q true' true   := by with_reducible apply_rfl -- NB: No error!
example : Q' true' true  := by with_reducible apply_rfl -- Error
example : R true' true   := by with_reducible apply_rfl -- Error

-- Equal at default transparency only

def true'' := true
def True'' := True

example : true'' = true   := by apply_rfl
example : HEq true'' true := by apply_rfl
example : True'' ↔ True   := by apply_rfl
example : P true'' true   := by apply_rfl
example : Q true'' true   := by apply_rfl
example : Q' true'' true  := by apply_rfl -- Error
example : R true'' true   := by apply_rfl -- Error

example : true'' = true   := by with_reducible apply_rfl -- Error
example : HEq true'' true := by with_reducible apply_rfl -- Error
example : True'' ↔ True   := by with_reducible apply_rfl -- Error
example : P true'' true   := by with_reducible apply_rfl -- Error
example : Q true'' true   := by with_reducible apply_rfl -- Error
example : Q' true'' true  := by with_reducible apply_rfl -- Error
example : R true'' true   := by with_reducible apply_rfl -- Error

-- Unequal
example : false = true   := by apply_rfl -- Error
example : HEq false true := by apply_rfl -- Error
example : False ↔ True   := by apply_rfl -- Error
example : P false true   := by apply_rfl -- Error
example : Q false true   := by apply_rfl -- Error
example : Q' false true  := by apply_rfl -- Error
example : R false true   := by apply_rfl -- Error

example : false = true   := by with_reducible apply_rfl -- Error
example : HEq false true := by with_reducible apply_rfl -- Error
example : False ↔ True   := by with_reducible apply_rfl -- Error
example : P false true   := by with_reducible apply_rfl -- Error
example : Q false true   := by with_reducible apply_rfl -- Error
example : Q' false true  := by with_reducible apply_rfl -- Error
example : R false true   := by with_reducible apply_rfl -- Error

-- Inheterogeneous unequal

example : HEq true 1 := by apply_rfl -- Error
example : HEq true 1 := by with_reducible apply_rfl -- Error

-- Rfl lemma with side condition:
-- Error message should show left-over goal

inductive S : Bool → Bool → Prop where | refl : a = true → S a a
attribute [refl] S.refl
example : S true false  := by apply_rfl -- Error
example : S true false  := by with_reducible apply_rfl -- Error
example : S true true   := by apply_rfl -- Error (left-over goal)
example : S true true   := by with_reducible apply_rfl -- Error (left-over goal)
example : S false false := by apply_rfl -- Error (left-over goal)
example : S false false := by with_reducible apply_rfl -- Error (left-over goal)
