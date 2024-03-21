import Lean.Elab.Command

#guard_msgs in
/-- error: unknown identifier 'x' -/
#guard_msgs in
example : α := x

/--
error: unknown identifier 'x'
---
error: ❌ Docstring on `#guard_msgs` does not match generated message:

error: unknown identifier 'x'
-/
#guard_msgs in
#guard_msgs in
example : α := x

#guard_msgs in
/-- warning: declaration uses 'sorry' -/
#guard_msgs in
example : α := sorry

#guard_msgs in
/-- warning: declaration uses 'sorry' -/
#guard_msgs(warning) in
example : α := sorry

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
#guard_msgs(error) in
example : α := sorry

#guard_msgs in
#guard_msgs(drop warning) in
example : α := sorry

#guard_msgs in
#guard_msgs(error, drop warning) in
example : α := sorry

#guard_msgs in
/-- error: unknown identifier 'x' -/
#guard_msgs(error, drop warning) in
example : α := x

#guard_msgs in
/--
error: failed to synthesize instance
  OfNat α 22
-/
#guard_msgs(error) in
example : α := 22

-- Trailing whitespace

/--
info: foo ⏎
bar
---
error: ❌ Docstring on `#guard_msgs` does not match generated message:

info: foo ⏎
bar
-/
#guard_msgs in
#guard_msgs in
run_meta Lean.logInfo "foo \nbar"

#guard_msgs in
/--
info: foo ⏎
bar
-/
#guard_msgs in
run_meta Lean.logInfo "foo \nbar"

/--
info: foo ⏎⏎
bar
---
error: ❌ Docstring on `#guard_msgs` does not match generated message:

info: foo ⏎⏎
bar
-/
#guard_msgs in
#guard_msgs in
run_meta Lean.logInfo "foo ⏎\nbar"

#guard_msgs in
/--
info: foo ⏎⏎
bar
-/
#guard_msgs in
run_meta Lean.logInfo "foo ⏎\nbar"
