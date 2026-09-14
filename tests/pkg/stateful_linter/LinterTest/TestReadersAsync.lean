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
• fi := 2
---
info: reader A(iii) sees
iii := 100
• ii := 10
  • i := 1
  • fi := 2
• fii := 20
• i := 1
• fi := 2
---
info: reader B(i) sees
i := 1
---
info: reader B(ii) sees
ii := 10
• i := 1
• fi := 2
---
info: reader B(iii) sees
iii := 100
• ii := 10
  • i := 1
  • fi := 2
• fii := 20
• i := 1
• fi := 2
---
info: reader C(i) sees
i := 1
---
info: reader C(ii) sees
ii := 10
• i := 1
• fi := 2
---
info: reader C(iii) sees
iii := 100
• ii := 10
  • i := 1
  • fi := 2
• fii := 20
• i := 1
• fi := 2
-/
#guard_msgs (ordering := sorted) in
def a1 := 1

/--
info: reader A(i) sees
i := 3
---
info: reader A(ii) sees
ii := 30
• i := 3
• fi := 4
---
info: reader A(iii) sees
iii := 300
• ii := 30
  • i := 3
  • fi := 4
• fii := 40
• i := 3
• fi := 4
---
info: reader B(i) sees
i := 3
---
info: reader B(ii) sees
ii := 30
• i := 3
• fi := 4
---
info: reader B(iii) sees
iii := 300
• ii := 30
  • i := 3
  • fi := 4
• fii := 40
• i := 3
• fi := 4
---
info: reader C(i) sees
i := 3
---
info: reader C(ii) sees
ii := 30
• i := 3
• fi := 4
---
info: reader C(iii) sees
iii := 300
• ii := 30
  • i := 3
  • fi := 4
• fii := 40
• i := 3
• fi := 4
-/
#guard_msgs (ordering := sorted) in
def a2 := 2

/--
info: reader A(i) sees
i := 5
---
info: reader A(ii) sees
ii := 50
• i := 5
• fi := 6
---
info: reader A(iii) sees
iii := 500
• ii := 50
  • i := 5
  • fi := 6
• fii := 60
• i := 5
• fi := 6
---
info: reader B(i) sees
i := 5
---
info: reader B(ii) sees
ii := 50
• i := 5
• fi := 6
---
info: reader B(iii) sees
iii := 500
• ii := 50
  • i := 5
  • fi := 6
• fii := 60
• i := 5
• fi := 6
---
info: reader C(i) sees
i := 5
---
info: reader C(ii) sees
ii := 50
• i := 5
• fi := 6
---
info: reader C(iii) sees
iii := 500
• ii := 50
  • i := 5
  • fi := 6
• fii := 60
• i := 5
• fi := 6
-/
#guard_msgs (ordering := sorted) in
def a3 := 3
