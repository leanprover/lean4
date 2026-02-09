/-
Test that try? supports user-defined suggestion generators via @[try_suggestion]
-/
module
public import Lean
public meta import Lean.Elab.Tactic.Try

open Lean Meta Elab Tactic Try

-- Define an opaque predicate that built-in tactics (including solve_by_elim) won't solve.
-- The axiom name starts with `_` so that `exact?` treats it as an implementation detail and
-- won't suggest it directly, allowing us to test user-defined suggestion generators.
opaque CustomProp : Prop
axiom _customPropHolds : CustomProp

section BasicTest
-- Define a generator that suggests the custom lemma
@[local try_suggestion]
meta def customPropSolver (_goal : MVarId) (_info : Try.Info) : MetaM (Array (TSyntax `tactic)) := do
  return #[← `(tactic| exact _customPropHolds)]

-- Test that try? picks up the user-defined suggestion
-- Built-in tactics won't solve this, so only user suggestion appears
/--
info: Try this:
  [apply] exact _customPropHolds✝
-/
#guard_msgs in
example : CustomProp := by
  try?
end BasicTest

section PriorityTest
-- Test priority ordering with multiple generators
@[local try_suggestion 2000]
meta def highPrioritySolver (_goal : MVarId) (_info : Try.Info) : MetaM (Array (TSyntax `tactic)) := do
  return #[← `(tactic| apply _customPropHolds)]

@[local try_suggestion 1000]
meta def midPrioritySolver (_goal : MVarId) (_info : Try.Info) : MetaM (Array (TSyntax `tactic)) := do
  return #[← `(tactic| exact _customPropHolds)]

@[local try_suggestion 500]
meta def lowPrioritySolver (_goal : MVarId) (_info : Try.Info) : MetaM (Array (TSyntax `tactic)) := do
  return #[← `(tactic| constructor)]

-- All generators return successful tactics, ordered by priority (highest first)
-- Note: constructor doesn't work on opaque types, so lowPrioritySolver's suggestion is filtered out
/--
info: Try these:
  [apply] apply _customPropHolds✝
  [apply] exact _customPropHolds✝
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
  [apply] solve_by_elim
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
  return #[← `(tactic| show_term apply _customPropHolds)]

-- Double-suggestion: when show_term produces a "Try this" message,
-- both the original tactic and the extracted suggestion should appear
-- The message from show_term during extraction is suppressed
/--
info: Try these:
  [apply] show_term apply _customPropHolds✝
  [apply] exact _customPropHolds
-/
#guard_msgs in
example : CustomProp := by
  try?
end DoubleSuggestion

section RegisterCommand
-- Test the register_try?_tactic convenience command
register_try?_tactic (priority := 500) exact _customPropHolds

/--
info: Try this:
  [apply] exact _customPropHolds
-/
#guard_msgs in
example : CustomProp := by
  try?

-- Test without explicit priority (should default to 1000, so appear before exact at 500)
register_try?_tactic apply _customPropHolds

/--
info: Try these:
  [apply] apply _customPropHolds
  [apply] exact _customPropHolds
-/
#guard_msgs in
example : CustomProp := by
  try?
end RegisterCommand
