import CQTest.Linters

/-!
Exercises capture of code quality entries in asynchronous mode (the default): every `def` makes
`linter.cqTest` log one entry, which must land in that command's slot of
`Command.State.codeQualityEntryTasks` and nowhere else. `hidden` is elaborated with the linter
option disabled, so its slot must be empty. The counts start with a `0` for this module
docstring command.
-/

def a1 := 1
def a2 := 2

set_option linter.cqTest false

def hidden := 3

set_option linter.cqTest true

/--
info: per-command entry counts: [0, 1, 1, 0, 0, 0]
---
info: captured entries: [a1, a2]
---
info: entries in current env: 0
-/
#guard_msgs in
#inspect_cq_entries
