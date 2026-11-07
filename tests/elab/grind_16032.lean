/-!
Regression test for #16032: `grind?` does not generate `· done` for a case-split alternative
that `grind` closes while introducing its hypotheses, since `cases` already closes it.
-/

def Holds (p : Nat → Prop) (a : Nat) := ∃ b, b = a ∧ p b

@[grind =] theorem holds_iff (p : Nat → Prop) (a : Nat) : Holds p a ↔ ∃ b, b = a ∧ p b := Iff.rfl

/--
info: Try these:
  [apply] grind only [= holds_iff, #6809, #86fa]
  [apply] grind only [= holds_iff]
  [apply] grind =>
    instantiate only [= holds_iff]
    cases #6809 <;> cases #86fa
-/
#guard_msgs in
example (p : Nat → Prop) (a : Nat) : Holds p a ↔ p a := by grind?

example (p : Nat → Prop) (a : Nat) : Holds p a ↔ p a := by
  grind only [= holds_iff, #6809, #86fa]

example (p : Nat → Prop) (a : Nat) : Holds p a ↔ p a := by
  grind only [= holds_iff]

example (p : Nat → Prop) (a : Nat) : Holds p a ↔ p a := by
  grind =>
    instantiate only [= holds_iff]
    cases #6809 <;> cases #86fa
