import system.IO

definition when (b : bool) (a : IO unit) : IO unit :=
if b = tt then a else return ()

vm_eval when tt (put_str "hello\n")
vm_eval when ff (put_str "error\n")
