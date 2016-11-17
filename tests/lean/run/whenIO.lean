import system.io

definition when (b : bool) (a : io unit) : io unit :=
if b = tt then a else return ()

vm_eval when tt (put_str "hello\n")
vm_eval when ff (put_str "error\n")
