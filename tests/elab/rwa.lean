module

import Lean
public import Lean.Elab.Term.TermElabM

/-!
# Tests for `rwa`

This tests first-goal isolation, discharging rewrite side goals, rewriting at hypotheses,
deprecated multi-location compatibility, and warnings when the final closing step is unnecessary.
-/

set_option linter.unusedVariables false
set_option linter.unnecessaryRwa true
set_option linter.deprecated.syntax true

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

example (ha : P a) (h : a = b) : P b := by
  rwa [h] at (ha : P a)

example {c : α} (ha : P a) (h₁ : a = b) (h₂ : b = c) : P c := by
  rwa [h₁, h₂] at (ha : P a)

example (ha : P a) (h : a = b) : P b := by
  rwa [h] at ‹P a›

/-- error: Unexpected term `ha rfl`; expected single reference to variable -/
#guard_msgs in
example (ha : a = a → p) : p := by
  rwa [] at (ha rfl)

-- The rewritten hypothesis, rather than another matching assumption, must close
-- the main goal.
example (ha : P a) (hq : q) (h : a = b) : q := by
  fail_if_success rwa [h] at ha
  exact hq

/--
error: Type mismatch: The rewritten hypothesis
  ha
has type
  P b
but is expected to have type
  q
-/
#guard_msgs in
example (ha : P a) (hq : q) (h : a = b) : q := by
  rwa [h] at ha

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

section EquationTheorems

/-!
Rewriting at a hypothesis with a definition that unfolds via equation theorems exercises the
retry across equation lemmas in `foldRWRulesSeq`, including threading the rewritten hypothesis
through to subsequent rules.
-/

private def shrink : Nat → Nat
  | 0 => 0
  | n + 1 => n

-- The first equation theorem does not apply, so rewriting must fall back to the second.
example {P : Nat → Prop} {n : Nat} (h : P (shrink (n + 1))) : P n := by
  rwa [shrink] at h

-- The hypothesis produced by the equation-theorem rewrite is rewritten by the next rule and
-- still closes the goal.
example {P : Nat → Prop} {n m : Nat} (h : P (shrink (n + 1))) (h' : n = m) : P m := by
  rwa [shrink, h'] at h

end EquationTheorems

section DeprecatedMultiLocation

variable {a b : α} {P Q R : α → Prop}

/--
warning: syntax 'Lean.Parser.Tactic.rwaAtLegacyLocation' has been deprecated: use `rw [...] at ... <;> assumption` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example (ha : P a) (hb : Q a) (hc : R a) (h : a = b) : P b := by
  rwa [h] at ha hb hc

/--
warning: syntax 'Lean.Parser.Tactic.rwaAtLegacyLocation' has been deprecated: use `rw [...] at ... <;> assumption` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example (S : Nat → Prop) (n : Nat) (h : S (0 + n)) : S n := by
  rwa [Nat.zero_add] at *

/--
warning: syntax 'Lean.Parser.Tactic.rwaAtLegacyLocation' has been deprecated: use `rw [...] at ... <;> assumption` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example (S : Nat → Prop) (n : Nat) (h : S n) : S (0 + n) := by
  rwa [Nat.zero_add] at ⊢

/--
warning: syntax 'Lean.Parser.Tactic.rwaAtLegacyLocation' has been deprecated: use `rw [...] at ... <;> assumption` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example (ha : P a) (h : a = b) : P a := by
  rwa [h] at ha ⊢

end DeprecatedMultiLocation

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
example (ha : P a) (hp : p) : (0 : Nat) = 0 := by
  rwa [conditionalEq a b p] at ha

/--
warning: `rw` already closes the goal

Hint: Use `rw` instead of `rwa`:
  [apply] rw [h] at ha

Note: This linter can be disabled with `set_option linter.unnecessaryRwa false`
-/
#guard_msgs in
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

/--
@ +3:2...17
error: No goals to be solved
-/
#guard_msgs (positions := true) in
example {a b c : Nat} (h : a = b) (h' : b = c) : a = c := by
  exact h.trans h'
  rwa [← h] at h'
