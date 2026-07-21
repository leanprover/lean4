import LinterTest.PreFailure

/- Asserts that a `pre` that throws is read by another linter's `post` as an absent handoff (`none`),
just like a decline — while a succeeding `pre` is read as `some`. `pf1` runs async (default), `pf2`
runs sync, so the pre-failure → `none` behaviour is pinned on both paths. A plain `/- -/` comment
avoids a counted module-doc command. -/

/--
error: stateful linter #0 (pre) failed: thrower boom
---
info: thrower: none, producer: some (42)
-/
#guard_msgs (ordering := sorted) in
def pf1 := 1

set_option Elab.async false in
/--
error: stateful linter #0 (pre) failed: thrower boom
---
info: thrower: none, producer: some (42)
-/
#guard_msgs (ordering := sorted) in
def pf2 := 2
