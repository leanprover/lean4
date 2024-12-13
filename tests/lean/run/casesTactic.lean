/-!
# Tests of the 'cases' tactic
-/

/-!
Error messages when not an inductive type.
-/

/--
error: tactic 'cases' failed, major premise type is not an inductive type
  Prop

Explanation: the 'cases' tactic is for constructor-based reasoning, with cases exhausting every way
in which a term could have been constructed. The 'Prop' universe is not an inductive type however,
so 'cases' does not apply. Consider using the 'by_cases' tactic, which enables true/false reasoning.
p : Prop
⊢ True
-/
#guard_msgs in
example (p : Prop) : True := by
  cases p

/--
error: tactic 'cases' failed, major premise type is not an inductive type
  Type

Explanation: the 'cases' tactic is for constructor-based reasoning, with cases exhausting every way
in which a term could have been constructed. Type universes are not inductive types however, so such
case-based reasoning is not possible. This is a strong limitation. According to Lean's underlying
theory, the only distinguishing feature of types is their cardinalities.
α : Type
⊢ True
-/
#guard_msgs in
example (α : Type) : True := by
  cases α

/--
error: tactic 'cases' failed, major premise type is not an inductive type
  Bool → Bool

Explanation: the 'cases' tactic is for constructor-based reasoning, with cases exhausting every way
in which a term could have been constructed. It can sometimes be helpful defining an equivalent
auxiliary inductive type to apply 'cases' to instead.
f : Bool → Bool
⊢ True
-/
#guard_msgs in
example (f : Bool → Bool) : True := by
  cases f
