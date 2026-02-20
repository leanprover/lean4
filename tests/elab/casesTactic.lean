/-!
# Tests of the 'cases' tactic
-/

/-!
Error messages when not an inductive type.
-/

/--
error: Tactic `cases` failed: major premise type is not an inductive type
  Prop

Explanation: the `cases` tactic is for constructor-based reasoning as well as for applying custom cases principles with a 'using' clause or a registered '@[cases_eliminator]' theorem. The above type neither is an inductive type nor has a registered theorem.

Consider using the 'by_cases' tactic, which does true/false reasoning for propositions.

p : Prop
⊢ True
-/
#guard_msgs in
example (p : Prop) : True := by
  cases p

/--
error: Tactic `cases` failed: major premise type is not an inductive type
  Type

Explanation: the `cases` tactic is for constructor-based reasoning as well as for applying custom cases principles with a 'using' clause or a registered '@[cases_eliminator]' theorem. The above type neither is an inductive type nor has a registered theorem.

Type universes are not inductive types, and type-constructor-based reasoning is not possible. This is a strong limitation. According to Lean's underlying theory, the only provable distinguishing feature of types is their cardinalities.

α : Type
⊢ True
-/
#guard_msgs in
example (α : Type) : True := by
  cases α

/--
error: Tactic `cases` failed: major premise type is not an inductive type
  Bool → Bool

Explanation: the `cases` tactic is for constructor-based reasoning as well as for applying custom cases principles with a 'using' clause or a registered '@[cases_eliminator]' theorem. The above type neither is an inductive type nor has a registered theorem.

f : Bool → Bool
⊢ True
-/
#guard_msgs in
example (f : Bool → Bool) : True := by
  cases f
