/--
warning: Add `import Lean.LibrarySuggestions.Basic` before using the `set_library_suggestions` command.
-/
#guard_msgs (warning, drop error) in
set_library_suggestions (fun _ _ => pure #[])
