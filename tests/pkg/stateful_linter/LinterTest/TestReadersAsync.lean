import LinterTest.Readers

/- Exercises the emitter/readers group in asynchronous mode (the default): each command makes `emitter`
count and the three readers report the count read from `emitter`'s pre-phase handoff, threaded across
commands via promises. A plain `/- -/` comment avoids a counted module-doc command. -/

/--
info: reader A sees count 1
---
info: reader B sees count 1
---
info: reader C sees count 1
-/
#guard_msgs (ordering := sorted) in
def a1 := 1

/--
info: reader A sees count 2
---
info: reader B sees count 2
---
info: reader C sees count 2
-/
#guard_msgs (ordering := sorted) in
def a2 := 2

/--
info: reader A sees count 3
---
info: reader B sees count 3
---
info: reader C sees count 3
-/
#guard_msgs (ordering := sorted) in
def a3 := 3
