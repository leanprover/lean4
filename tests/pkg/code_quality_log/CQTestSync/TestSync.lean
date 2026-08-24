import CQTest.Linters

/-!
Same as `CQTest.TestAsync`, but the whole file is elaborated under `Elab.async false` (set via
`leanOptions` in the lakefile), exercising the synchronous branch of `runLintersAsync` where
`runLinters` runs inside `withoutModifyingEnv` and resolves the promise on the spot.
-/

def s1 := 1
def s2 := 2

set_option linter.cqTest false

def hidden := 3

set_option linter.cqTest true

/--
info: per-command entry counts: [0, 1, 1, 0, 0, 0]
---
info: captured entries: [s1, s2]
---
info: entries in current env: 0
-/
#guard_msgs in
#inspect_cq_entries
