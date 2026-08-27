module

import Lean
public import Lean.Elab.Term.TermElabM

/-!
# Tests for `rwa`

This tests first-goal isolation, discharging rewrite side goals, rewriting at a
hypothesis, and warnings when the final closing step is unnecessary.
-/

set_option linter.unnecessaryRwa true

section SuggestionValidation

set_option linter.unnecessarySimpa true

elab "validation_sensitive% " t:term : term => do
  unless (← read).errToSorry do
    throwError "the term cannot be replayed without recovery"
  return ← Lean.Elab.Term.elabTerm t none

/-!
An invalid replacement is not offered as an applicable hint, even though the
linter warning itself is still emitted.
-/

/--
warning: `rw` already closes the goal

Note: This linter can be disabled with `set_option linter.unnecessaryRwa false`
-/
#guard_msgs in
example (h : n = m) : n = m := by
  rwa [validation_sensitive% h]

private def suggestionValidationFoo (n : α) := [n]
private theorem suggestionValidationFoo_eq (n : α) : suggestionValidationFoo n = [n] := rfl

/--
warning: `simp` already closes the goal

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
-/
#guard_msgs in
example : suggestionValidationFoo n = [n] := by
  simpa only [validation_sensitive% suggestionValidationFoo_eq]

end SuggestionValidation

section Basic

variable {p q : Prop}

example (hp : p) (h : p ↔ q) : q := by
  rwa [← h]

set_option linter.unnecessaryRwa false in
example (h : n = m) : n = m ∧ True := by
  constructor
  rwa [h]
  trivial

example : True := by
  fail_if_success rwa []
  trivial

end Basic

section SideGoals

variable {p : Prop} {a b : α} {P : α → Prop}

axiom conditionalEq (a b : α) (p : Prop) : p → a = b

example (hb : P b) (hp : p) : P a := by
  rwa [conditionalEq a b p]

example (hb : P b) (mkp : True → p) : P a := by
  rwa [conditionalEq a b p]
  exact mkp trivial

end SideGoals

section AtHypothesis

variable {p q : Prop} {a b : α} {P : α → Prop}

example (ha : P a) (h : a = b) : P b := by
  rwa [h] at ha

-- The rewritten hypothesis, rather than another matching assumption, must close
-- the main goal.
set_option linter.unusedVariables false in
example (ha : P a) (hq : q) (h : a = b) : q := by
  fail_if_success rwa [h] at ha
  exact hq

example (ha : P a) (hp : p) : P b := by
  rwa [conditionalEq a b p] at ha

example (ha : P a) (mkp : True → p) : P b := by
  rwa [conditionalEq a b p] at ha
  exact mkp trivial

set_option linter.unnecessaryRwa false in
example (ha : P a) (h : a = b) : P b ∧ True := by
  constructor
  rwa [h] at ha
  trivial

end AtHypothesis

section Unnecessary

variable {p q : Prop} {a b : α} {P : α → Prop}

/-!
When `rw` closes the goal by reflexivity, the final `assumption` is unnecessary.
-/

/--
warning: `rw` already closes the goal

Hint: Use `rw` instead of `rwa`:
  [apply] rw [h]

Note: This linter can be disabled with `set_option linter.unnecessaryRwa false`
-/
#guard_msgs in
example (h : n = m) : n = m := by
  rwa [h]

/-!
No warning is emitted when rewriting produces side goals, whether or not `rwa`
can close them using `assumption`.
-/

#guard_msgs in
example (mkp : True → p) : a = b := by
  rwa [conditionalEq a b p]
  exact mkp trivial

#guard_msgs in
example (hp : p) : a = b := by
  rwa [conditionalEq a b p]

#guard_msgs in
set_option linter.unusedVariables false in
example (ha : P a) (hp : p) : (0 : Nat) = 0 := by
  rwa [conditionalEq a b p] at ha

/--
warning: `rw` already closes the goal

Hint: Use `rw` instead of `rwa`:
  [apply] rw [h] at ha

Note: This linter can be disabled with `set_option linter.unnecessaryRwa false`
-/
#guard_msgs in
set_option linter.unusedVariables false in
example (ha : P a) (h : a = b) : (0 : Nat) = 0 := by
  rwa [h] at ha

#guard_msgs in
set_option linter.unnecessaryRwa false in
example (h : n = m) : n = m := by
  rwa [h]

#guard_msgs in
example (hp : p) (h : p ↔ q) : q := by
  rwa [← h]

end Unnecessary

/--
warning: `rw` already closes the goal

Hint: Use `rw` instead of `rwa`:
  [apply] rw [h]

Note: This linter can be disabled with `set_option linter.unnecessaryRwa false`
-/
#guard_msgs in
example {a b c : Nat} (h : a = b) (h' : b = c) : a = b ∧ b = c := by
  constructor
  rwa [h]
  exact h'
