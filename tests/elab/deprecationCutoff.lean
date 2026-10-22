module

import Lean

/-! Date cutoffs suppress deprecation warnings without changing elaboration or metadata. -/

set_option linter.deprecated true
set_option linter.deprecated.syntax true
set_option deprecation.warnings "1900-01-01"
set_option deprecation.warnings.local "2024-02-29"

@[deprecated "before the cutoff" (since := "2024-02-28")]
def beforeCutoff : Nat := 1

@[deprecated "at the cutoff" (since := "2024-02-29")]
def atCutoff : Nat := 2

@[deprecated "after the cutoff" (since := "2024-03-01")]
def afterCutoff : Nat := 3

/-- warning: `beforeCutoff` has been deprecated: before the cutoff -/
#guard_msgs in
example : Nat := beforeCutoff

/-- warning: `atCutoff` has been deprecated: at the cutoff -/
#guard_msgs in
example : Nat := atCutoff

#guard_msgs in
example : Nat := afterCutoff

/-- warning: `afterCutoff` has been deprecated: after the cutoff -/
#guard_msgs in
set_option deprecation.warnings.local "all" in
example : Nat := afterCutoff

#guard_msgs in
example : Nat := afterCutoff

#guard_msgs in
set_option linter.deprecated false in
example : Nat := beforeCutoff

run_cmd do
  unless Lean.Linter.isDeprecated (← Lean.getEnv) ``afterCutoff do
    throwError "the cutoff must not change deprecation metadata"

@[deprecated "invalid date" (since := "2024-02-30")]
def invalidSince : Nat := 0

@[deprecated "legacy version" (since := "v4.37.0")]
def versionSince : Nat := 0

def noSince : Nat := 0
run_cmd Lean.Linter.setDeprecated ``noSince { text? := some "no date" }

/-- warning: `invalidSince` has been deprecated: invalid date -/
#guard_msgs in
example : Nat := invalidSince

/-- warning: `versionSince` has been deprecated: legacy version -/
#guard_msgs in
example : Nat := versionSince

/-- warning: `noSince` has been deprecated: no date -/
#guard_msgs in
example : Nat := noSince

@[deprecated_arg old new (since := "2024-03-01")]
def renamed (new : Nat) : Nat := new

#guard_msgs in
example : renamed (old := 7) = 7 := rfl

/-- warning: parameter `old` of `renamed` has been deprecated, use `new` instead -/
#guard_msgs (substring := true) in
set_option deprecation.warnings.local "all" in
example : Nat := renamed (old := 7)

@[deprecated_arg removed "no longer accepted" (since := "2024-03-01")]
def removed : Nat := 0

/-- error: parameter `removed` of `removed` has been deprecated: no longer accepted -/
#guard_msgs (substring := true) in
#check removed (removed := 7)

syntax (name := delayedTerm) "delayed_term" : term
macro_rules | `(delayed_term) => `(1)
deprecated_syntax delayedTerm "use `1`" (since := "2024-03-01")

#guard_msgs in
example : Nat := delayed_term

#guard_msgs in
macro "quoted_delayed_term" : term => ``(delayed_term)

/-- warning: syntax 'delayedTerm' has been deprecated: use `1` -/
#guard_msgs (substring := true) in
set_option deprecation.warnings.local "all" in
example : Nat := delayed_term

/-- warning: quotation uses deprecated syntax 'delayedTerm': use `1` -/
#guard_msgs (substring := true) in
set_option deprecation.warnings.local "all" in
macro "quoted_noisy_term" : term => ``(delayed_term)

syntax (name := delayedTactic) "delayed_tactic" : tactic
macro_rules | `(tactic| delayed_tactic) => `(tactic| trivial)
deprecated_syntax delayedTactic (since := "2024-03-01")

#guard_msgs in
example : True := by delayed_tactic

syntax (name := delayedCommand) "delayed_command" : command
macro_rules | `(delayed_command) => `(example : True := trivial)
deprecated_syntax delayedCommand (since := "2024-03-01")

#guard_msgs in
delayed_command

-- This deprecation is serialized by stage0 when building Init.
#guard_msgs in
example {α : Type} {a b : α} {P Q : α → Prop}
    (ha : P a) (hb : Q a) (h : a = b) : P b := by
  rwa [h] at ha hb

/-- warning: syntax 'Lean.Parser.Tactic.rwaAtLegacyLocation' has been deprecated -/
#guard_msgs (substring := true) in
set_option deprecation.warnings.local "all" in
example {α : Type} {a b : α} {P Q : α → Prop}
    (ha : P a) (hb : Q a) (h : a = b) : P b := by
  rwa [h] at ha hb

def replacement : Nat := 0

/-- warning: The `+typeChanged` marker is not needed because the updated constant has the same type. -/
#guard_msgs in
@[deprecated replacement +typeChanged (since := "2024-03-01")]
def redundantTypeChanged : Nat := 0

/-- error: Invalid value for `deprecation.warnings`: expected "all" or a date in YYYY-MM-DD format -/
#guard_msgs in
set_option deprecation.warnings "2023-02-29"

/-- error: Invalid value for `deprecation.warnings.local`: expected "all" or a date in YYYY-MM-DD format -/
#guard_msgs in
set_option deprecation.warnings.local "2024-2-29"

/-- error: Invalid value for `deprecation.warnings`: expected "all" or a date in YYYY-MM-DD format -/
#guard_msgs in
set_option deprecation.warnings "v4.37.0"

/-- error: Invalid value for `deprecation.warnings.local`: expected "all" or a date in YYYY-MM-DD format -/
#guard_msgs in
set_option deprecation.warnings.local "today"

/-- error: Invalid value for `deprecation.warnings`: expected "all" or a date in YYYY-MM-DD format -/
#guard_msgs in
set_option deprecation.warnings ""

#guard_msgs in
set_option deprecation.warnings "2024-02-29"
