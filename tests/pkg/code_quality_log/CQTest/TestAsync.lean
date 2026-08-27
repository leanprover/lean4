import CQTest.Linters

/-!
Exercises capture of code quality entries in asynchronous mode (the default): every `def` makes
the regular linter and the stateful linter log one entry each, which must land in that command's
regular- and stateful-linter slots of `Command.State.codeQualityEntryTasks` and nowhere else.
`hidden` is elaborated with the linter option disabled, so its slots must be empty. The counts
come in triples per command (regular, module, stateful linters), starting with a triple of zeros
for this module docstring command.
-/

def a1 := 1
def a2 := 2

set_option linter.cqTest false

def hidden := 3

set_option linter.cqTest true

/--
info: per-command entry counts: [0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
---
info: captured entries: [a1, stateful:a1:1, a2, stateful:a2:2]
---
info: entries in current env: 0
-/
#guard_msgs in
#inspect_cq_entries
