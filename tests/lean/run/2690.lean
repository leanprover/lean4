/-!
# `Prop`-valued `inductive`/`structure` by default

When the inductive types are syntactic subsingletons and could be `Prop`,
they may as well be `Prop`.

Issue: https://github.com/leanprover/lean4/issues/2690
-/

/-!
Subsingleton, but no constructors. Type.
-/
inductive I0 where
/-- info: I0 : Type -/
#guard_msgs in #check I0

/-!
One constructor, has a Prop parameter. Prop.
-/
inductive I1 where
  | a (h : True)
/-- info: I1 : Prop -/
#guard_msgs in #check I1

/-!
One constructor, no constructor parameters. Type.
-/
inductive I2 where
  | a
/-- info: I2 : Type -/
#guard_msgs in #check I2

inductive I2' (_ : Nat) where
  | a
/-- info: I2' : Nat → Type -/
#guard_msgs in #check I2'

/-!
Two constructors. Type
-/
inductive I3 where
  | a | b
/-- info: I3 : Type -/
#guard_msgs in #check I3

/-!
Mutually inductives, both syntactic subsingletons,
even if one doesn't have a constructor,
and one has no parameters.
-/
mutual
inductive C1 where
inductive C2 where
  | a (h : True)
inductive C3 where
  | b
end
/-- info: C1 : Prop -/
#guard_msgs in #check C1
/-- info: C2 : Prop -/
#guard_msgs in #check C2
/-- info: C3 : Prop -/
#guard_msgs in #check C3

/-!
Type parameter (promoted from index), still Prop.
-/
inductive D : Nat → Sort _ where
  | a (h : n = n) : D n
/-- info: D : Nat → Prop -/
#guard_msgs in #check D

/-!
Structure with no fields, Type.
-/
structure S1 where
/-- info: S1 : Type -/
#guard_msgs in #check S1

/-!
Structure with a Prop field, Prop.
-/
structure S2 where
  h : True
/-- info: S2 : Prop -/
#guard_msgs in #check S2

/-!
Structure with parameter and a Prop field, Prop.
-/
structure S3 (α : Type) where
  h : ∀ a : α, a = a
/-- info: S3 (α : Type) : Prop -/
#guard_msgs in #check S3

/-!
Verify: `Decidable` is a `Type`.
-/
class inductive Decidable' (p : Prop) where
  | isFalse (h : Not p) : Decidable' p
  | isTrue (h : p) : Decidable' p
/-- info: Decidable' (p : Prop) : Type -/
#guard_msgs in #check Decidable'

/-!
Verify: `WellFounded` is a `Prop`.
-/
inductive WellFounded' {α : Sort u} (r : α → α → Prop) where
  | intro (h : ∀ a, Acc r a) : WellFounded' r
/-- info: WellFounded'.{u} {α : Sort u} (r : α → α → Prop) : Prop -/
#guard_msgs in #check WellFounded'
