
/-!
This file tests the `rfl` tactic:
 * Extensibility
 * Error messages
 * Effect of `with_reducible`
-/

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

example : true = true   := by rfl
example : HEq true true := by rfl
example : True ↔ True   := by rfl
example : P true true   := by rfl
example : Q true true   := by rfl
example : Q' true true  := by rfl -- Error
example : R true true   := by rfl -- Error

example : true = true   := by with_reducible rfl
example : HEq true true := by with_reducible rfl
example : True ↔ True   := by with_reducible rfl
example : P true true   := by with_reducible rfl
example : Q true true   := by with_reducible rfl
example : Q' true true  := by with_reducible rfl -- Error
example : R true true   := by with_reducible rfl -- Error

-- Reducibly equal

abbrev true' := true
abbrev True' := True

example : true' = true   := by rfl
example : HEq true' true := by rfl
example : True' ↔ True   := by rfl
example : P true' true   := by rfl
example : Q true' true   := by rfl
example : Q' true' true  := by rfl -- Error
example : R true' true   := by rfl -- Error

example : true' = true   := by with_reducible rfl
example : HEq true' true := by with_reducible rfl
example : True' ↔ True   := by with_reducible rfl
example : P true' true   := by with_reducible rfl
example : Q true' true   := by with_reducible rfl -- NB: No error!
example : Q' true' true  := by with_reducible rfl -- Error
example : R true' true   := by with_reducible rfl -- Error

-- Equal at default transparency only

def true'' := true
def True'' := True

example : true'' = true   := by rfl
example : HEq true'' true := by rfl
example : True'' ↔ True   := by rfl
example : P true'' true   := by rfl
example : Q true'' true   := by rfl
example : Q' true'' true  := by rfl -- Error
example : R true'' true   := by rfl -- Error

example : true'' = true   := by with_reducible rfl -- Error
example : HEq true'' true := by with_reducible rfl -- Error
example : True'' ↔ True   := by with_reducible rfl -- Error
example : P true'' true   := by with_reducible rfl -- Error
example : Q true'' true   := by with_reducible rfl -- Error
example : Q' true'' true  := by with_reducible rfl -- Error
example : R true'' true   := by with_reducible rfl -- Error

-- Unequal
example : false = true   := by rfl -- Error
example : HEq false true := by rfl -- Error
example : False ↔ True   := by rfl -- Error
example : P false true   := by rfl -- Error
example : Q false true   := by rfl -- Error
example : Q' false true  := by rfl -- Error
example : R false true   := by rfl -- Error

example : false = true   := by with_reducible rfl -- Error
example : HEq false true := by with_reducible rfl -- Error
example : False ↔ True   := by with_reducible rfl -- Error
example : P false true   := by with_reducible rfl -- Error
example : Q false true   := by with_reducible rfl -- Error
example : Q' false true  := by with_reducible rfl -- Error
example : R false true   := by with_reducible rfl -- Error

-- Inheterogeneous unequal

example : HEq true 1 := by rfl -- Error
example : HEq true 1 := by with_reducible rfl -- Error

-- Rfl lemma with side condition:
-- Error message should show left-over goal

inductive S : Bool → Bool → Prop where | refl : a = true → S a a
attribute [refl] S.refl
example : S true false  := by rfl -- Error
example : S true false  := by with_reducible rfl -- Error
example : S true true   := by rfl -- Error (left-over goal)
example : S true true   := by with_reducible rfl -- Error (left-over goal)
example : S false false := by rfl -- Error (left-over goal)
example : S false false := by with_reducible rfl -- Error (left-over goal)
