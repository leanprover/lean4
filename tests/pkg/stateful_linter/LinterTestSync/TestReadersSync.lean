import LinterTest.Readers

/- Exercises the emitter/readers group in synchronous mode. The whole file runs sync via this
library's `leanOptions := #[⟨`Elab.async, false⟩]` in the lakefile — no in-file `set_option` (which
would be a counted command that leaks the linter's output). A plain `/- -/` comment avoids a counted
module-doc command. -/

/--
info: reader A sees count 1
---
info: reader B sees count 1
---
info: reader C sees count 1
-/
#guard_msgs (ordering := sorted) in
def s1 := 1

/--
info: reader A sees count 2
---
info: reader B sees count 2
---
info: reader C sees count 2
-/
#guard_msgs (ordering := sorted) in
def s2 := 2

/--
info: reader A sees count 3
---
info: reader B sees count 3
---
info: reader C sees count 3
-/
#guard_msgs (ordering := sorted) in
def s3 := 3
