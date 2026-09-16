import CQTest.Linters

/-!
Exercises capture of code quality entries in asynchronous mode (the default): every `def` makes
the regular linter log an attributed and an unattributed entry and the stateful linter log one
attributed entry, which must land in that command's regular- and stateful-linter slots of
`Command.State.codeQualityEntryTasks` and nowhere else. `hidden` is elaborated with the linter
option disabled, so only the unattributed `raw:` entry (which the option does not gate) is
captured for it. The counts come in triples per command (regular, module, stateful linters),
starting with a triple of zeros for this module docstring command.
-/

def a1 := 1
def a2 := 2

set_option linter.cqTest false

def hidden := 3

set_option linter.cqTest true

/--
info: per-command entry counts: [0, 0, 0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0]
---
info: captured entries: [linter.cqTest/a1, _/raw:a1, linter.cqTest/stateful:a1:1, linter.cqTest/a2, _/raw:a2, linter.cqTest/stateful:a2:2, _/raw:hidden]
---
info: entries in current env: 0
-/
#guard_msgs in
#inspect_cq_entries
