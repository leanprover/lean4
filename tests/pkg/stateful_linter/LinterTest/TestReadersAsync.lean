import LinterTest.Readers

/- Exercises the emitter/readers group in asynchronous mode (the default): each command makes `emitter`
count and the three readers report the count read from `emitter`'s pre-phase handoff, threaded across
commands via promises. A plain `/- -/` comment avoids a counted module-doc command. -/

/--
info: reader A(i) sees
i := 1
---
info: reader A(ii) sees
ii := 10
• i := 1
---
info: reader A(iii) sees
iii := 100
• ii := 10
  • i := 1
• i := 1
---
info: reader B(i) sees
i := 1
---
info: reader B(ii) sees
ii := 10
• i := 1
---
info: reader B(iii) sees
iii := 100
• ii := 10
  • i := 1
• i := 1
---
info: reader C(i) sees
i := 1
---
info: reader C(ii) sees
ii := 10
• i := 1
---
info: reader C(iii) sees
iii := 100
• ii := 10
  • i := 1
• i := 1
-/
#guard_msgs (ordering := sorted) in
def a1 := 1

/--
info: reader A(i) sees
i := 2
@[inclusion ⊢ id]
@[inclusion ⊣ id] (or @[inclusion id ⊢])

@[inclusion → id]
@[inclusion ← id]

@[inclusion ↑ id]
@[inclusion ↓ id]

@[inclusion id]
@[inclusion_hyp id]
---
info: reader A(ii) sees
ii := 20
• i := 2
---
info: reader A(iii) sees
iii := 200
• ii := 20
  • i := 2
• i := 2
---
info: reader B(i) sees
i := 2
---
info: reader B(ii) sees
ii := 20
• i := 2
---
info: reader B(iii) sees
iii := 200
• ii := 20
  • i := 2
• i := 2
---
info: reader C(i) sees
i := 2
---
info: reader C(ii) sees
ii := 20
• i := 2
---
info: reader C(iii) sees
iii := 200
• ii := 20
  • i := 2
• i := 2
-/
#guard_msgs (ordering := sorted) in
def a2 := 2

/--
info: reader A(i) sees
i := 3
---
info: reader A(ii) sees
ii := 30
• i := 3
---
info: reader A(iii) sees
iii := 300
• ii := 30
  • i := 3
• i := 3
---
info: reader B(i) sees
i := 3
---
info: reader B(ii) sees
ii := 30
• i := 3
---
info: reader B(iii) sees
iii := 300
• ii := 30
  • i := 3
• i := 3
---
info: reader C(i) sees
i := 3
---
info: reader C(ii) sees
ii := 30
• i := 3
---
info: reader C(iii) sees
iii := 300
• ii := 30
  • i := 3
• i := 3
-/
#guard_msgs (ordering := sorted) in
def a3 := 3
