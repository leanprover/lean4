import LinterTest.Errors

/- Error handling on both stateful-linter paths: `ea` runs async (default), `eb` runs sync (via
`set_option Elab.async false in`). Each command logs both throwers' errors *and* the working
`counter`'s count, showing that a failing linter is logged, isolated from the others, and non-fatal to
threading (the count keeps advancing). A plain `/- -/` comment avoids a counted module-doc command. -/

/--
info: count: 1
---
error: stateful linter LinterTest.Errors.thrower (#0) failed:
  boom
-/
#guard_msgs in
def ea := 1

set_option Elab.async false in
/--
info: count: 2
---
error: stateful linter LinterTest.Errors.thrower (#0) failed:
  boom
-/
#guard_msgs in
def eb := 2
