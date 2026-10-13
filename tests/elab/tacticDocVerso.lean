import Lean

/-!
Tests that the documentation comments of tactic tags and tactic extensions are stored as Markdown,
both when they are written in Markdown and when they are parsed as Verso.
-/

open Lean Elab Command Parser.Tactic.Doc

/-- Tactics that close goals with *arithmetic* -/
register_tactic_tag markdownTag "markdown tag"

set_option doc.verso true in
/-- Tactics that reduce {name}`Nat.succ` applications, *eagerly* -/
register_tactic_tag versoTag "verso tag"

/-- info: some ("markdown tag", some "Tactics that close goals with *arithmetic*") -/
#guard_msgs in
#eval show CommandElabM _ from tagInfo `markdownTag

/-- info: some ("verso tag", some "Tactics that reduce `Nat.succ` applications, **eagerly** ") -/
#guard_msgs in
#eval show CommandElabM _ from tagInfo `versoTag

/-- A tactic to extend -/
syntax (name := extendMe) "extend_me" : tactic

/-- It also accepts *arithmetic* goals -/
tactic_extension extendMe

set_option doc.verso true in
/-- It also reduces {name}`Nat.succ`, *eagerly* -/
tactic_extension extendMe

/--
info: #["It also accepts *arithmetic* goals", "It also reduces `Nat.succ`, **eagerly** "]
-/
#guard_msgs in
#eval show CommandElabM _ from return getTacticExtensions (← getEnv) ``extendMe
