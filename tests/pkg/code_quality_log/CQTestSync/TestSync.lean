import CQTest.Linters

/-!
Same as `CQTest.TestAsync`, but the whole file is elaborated under `Elab.async false` (set via
`leanOptions` in the lakefile), exercising the synchronous branches of `runLintersAsync` and
`runStatefulLintersAsync`, where the linters run inside `withoutModifyingEnv` and resolve their
promises on the spot.
-/

def s1 := 1
def s2 := 2

set_option linter.cqTest false

def hidden := 3

set_option linter.cqTest true

/--
info: per-command entry counts: [0, 0, 0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0]
---
info: captured entries: [linter.cqTest/s1, _/raw:s1, linter.cqTest/stateful:s1:1, linter.cqTest/s2, _/raw:s2, linter.cqTest/stateful:s2:2, _/raw:hidden]
---
info: entries in current env: 0
-/
#guard_msgs in
#inspect_cq_entries
