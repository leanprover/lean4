/--
warning: Add `import Lean.PremiseSelection.Basic` before using the `set_premise_selector` command.
-/
#guard_msgs (warning, drop error) in
set_premise_selector (fun _ _ => pure #[])
