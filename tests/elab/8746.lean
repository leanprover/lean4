/-!
Regression test for #8746: with `Elab.async false`, messages reported by `addDecl` such as
`declaration uses sorry` used to be ordered differently in `#guard_msgs` than with `Elab.async`.
-/

/--
trace: hi
---
warning: declaration uses `sorry`
-/
#guard_msgs in
theorem async : True := by
  trace "hi"
  sorry

set_option Elab.async false

/--
trace: hi
---
warning: declaration uses `sorry`
-/
#guard_msgs in
theorem sync : True := by
  trace "hi"
  sorry

/--
trace: hi
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : True := by
  trace "hi"
  sorry
