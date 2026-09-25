import LinterTest.ModeSwitch

/- Threads the command count across `Elab.async` mode switches. `ma`/`mc` run async (the default);
`mb`/`md` run sync via `set_option Elab.async false in` wrapping the `#guard_msgs in def` (so the
option is in scope when the linter runs on the inner `def`, and the outer command is skipped as it
contains `#guard_msgs`). The count must stay sequential across every transition. -/

/-- info: count: 1 -/
#guard_msgs in
def ma := 1

set_option Elab.async false in
/-- info: count: 2 -/
#guard_msgs in
def mb := 2

/-- info: count: 3 -/
#guard_msgs in
def mc := 3

set_option Elab.async false in
/-- info: count: 4 -/
#guard_msgs in
def md := 4
