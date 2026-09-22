import CQTest.Linters

/-!
Exercises capture of code quality entries in asynchronous mode (the default): every `def` makes
the regular linter log an attributed and an unattributed entry and the stateful linter log one
attributed entry. The entries are captured per command in `Command.State.codeQualityEntryTasks`,
handed over to the command's snapshot, and merged into the final environment by `runFrontend`;
`PrintEntries.lean` checks what was persisted for this module. `hidden` is elaborated with the
linter option disabled, so only the unattributed `raw:` entry (which the option does not gate)
is recorded for it.
-/

def a1 := 1
def a2 := 2

set_option linter.cqTest false

def hidden := 3

set_option linter.cqTest true

/--
info: capture tasks in state: 0
---
info: entries in current env: 0
-/
#guard_msgs in
#inspect_cq_state
