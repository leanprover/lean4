/-
Test that try? supports user-defined suggestion generators via @[try_suggestion]
-/
module
public import Lean
public meta import Lean.Elab.Tactic.Try

open Lean Meta Elab Tactic Try

-- Define a custom inductive predicate that built-in tactics won't solve automatically
inductive CustomProp : Prop where
  | mk : CustomProp

-- Lemma about CustomProp
theorem customPropHolds : CustomProp := CustomProp.mk

section BasicTest
-- Define a generator that suggests the custom lemma
@[local try_suggestion]
meta def customPropSolver (_goal : MVarId) (_info : Try.Info) : MetaM (Array (TSyntax `tactic)) := do
  return #[← `(tactic| exact CustomProp.mk)]

-- Test that try? picks up the user-defined suggestion
-- Built-in tactics won't solve this, so only user suggestion appears
/--
info: Try this:
  [apply] exact CustomProp.mk✝
-/
#guard_msgs in
example : CustomProp := by
  try?
end BasicTest

section PriorityTest
-- Test priority ordering with multiple generators
@[local try_suggestion 2000]
meta def highPrioritySolver (_goal : MVarId) (_info : Try.Info) : MetaM (Array (TSyntax `tactic)) := do
  return #[← `(tactic| apply CustomProp.mk)]

@[local try_suggestion 1000]
meta def midPrioritySolver (_goal : MVarId) (_info : Try.Info) : MetaM (Array (TSyntax `tactic)) := do
  return #[← `(tactic| exact CustomProp.mk)]

@[local try_suggestion 500]
meta def lowPrioritySolver (_goal : MVarId) (_info : Try.Info) : MetaM (Array (TSyntax `tactic)) := do
  return #[← `(tactic| constructor)]

-- All generators return successful tactics, ordered by priority (highest first)
/--
info: Try these:
  [apply] apply CustomProp.mk✝
  [apply] exact CustomProp.mk✝
  [apply] constructor
-/
#guard_msgs in
example : CustomProp := by
  try?
end PriorityTest

section BuiltInFallback
-- Test that user generators only run if built-ins fail
-- For True, built-ins succeed so user generators shouldn't run
@[local try_suggestion]
meta def shouldNotRunForTrue (_goal : MVarId) (_info : Try.Info) : MetaM (Array (TSyntax `tactic)) := do
  return #[← `(tactic| exact True.intro)]

-- Built-ins succeed, so user suggestion doesn't appear
/--
info: Try these:
  [apply] simp
  [apply] simp only
  [apply] grind
  [apply] grind only
  [apply] simp_all
-/
#guard_msgs in
example : True := by
  try?
end BuiltInFallback

section DoubleSuggestion
-- Test double-suggestion: when a user tactic produces "Try this" messages,
-- both the original tactic and the suggestions should appear
-- Use CustomProp which built-ins can't solve
@[local try_suggestion]
meta def doubleSuggestionSolver (_goal : MVarId) (_info : Try.Info) : MetaM (Array (TSyntax `tactic)) := do
  return #[← `(tactic| show_term apply CustomProp.mk)]

-- Double-suggestion: when show_term produces a "Try this" message,
-- both the original tactic and the extracted suggestion should appear
-- The message from show_term during extraction is suppressed
/--
info: Try these:
  [apply] show_term apply CustomProp.mk✝
  [apply] exact CustomProp.mk
-/
#guard_msgs in
example : CustomProp := by
  try?
end DoubleSuggestion
