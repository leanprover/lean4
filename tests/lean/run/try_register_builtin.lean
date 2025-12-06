/-
Test that register_try?_tactic works as a builtin command
The syntax is available without any imports, but it warns when Lean.Elab.Tactic.Try is not imported
-/

-- Custom predicate for testing
inductive MyProp : Prop where
  | intro : MyProp

/--
warning: Add `import Lean.Elab.Tactic.Try` before using the `register_try?_tactic` command.
-/
#guard_msgs in
register_try?_tactic exact MyProp.intro
