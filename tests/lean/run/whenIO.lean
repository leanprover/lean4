import system.IO
open bool unit

definition when (b : bool) (a : IO unit) : IO unit :=
cond b a (return star)

vm_eval when tt (put_str "hello\n")
vm_eval when ff (put_str "error\n")
